/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C016
import LeanDring.P5.Data.EntryK.C017

/-!
# Species-table cells, off-support emptiness certificates, chunk 61

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

theorem fixz1_69 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK69) (retConj 1 (R69 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_69_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨1, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 1 (by decide)))

theorem fz1_69_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨2, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 2 (by decide)))

theorem fz1_69_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨3, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 3 (by decide)))

theorem fz1_69_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨4, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 4 (by decide)))

theorem fz1_69_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨5, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 5 (by decide)))

theorem fz1_69_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨6, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 6 (by decide)))

theorem fz1_69_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨7, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 7 (by decide)))

theorem fz1_69_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨9, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 9 (by decide)))

theorem fz1_69_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨10, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 10 (by decide)))

theorem fz1_69_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨11, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 11 (by decide)))

theorem fz1_69_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨13, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 13 (by decide)))

theorem fz1_69_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨14, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 14 (by decide)))

theorem fz1_69_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨15, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 15 (by decide)))

theorem fz1_69_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨16, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 16 (by decide)))

theorem fz1_69_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨17, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 17 (by decide)))

theorem fz1_69_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨18, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 18 (by decide)))

theorem fz1_69_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨19, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 19 (by decide)))

theorem fz1_69_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨20, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 20 (by decide)))

theorem fz1_69_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨21, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 21 (by decide)))

theorem fz1_69_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨22, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 22 (by decide)))

theorem fz1_69_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨23, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 23 (by decide)))

theorem fz1_69_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨24, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 24 (by decide)))

theorem fz1_69_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨25, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 25 (by decide)))

theorem fz1_69_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨27, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 27 (by decide)))

theorem fz1_69_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨28, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 28 (by decide)))

theorem fz1_69_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨29, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 29 (by decide)))

theorem fz1_69_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨31, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 31 (by decide)))

theorem fz1_69_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨32, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 32 (by decide)))

theorem fz1_69_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨33, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 33 (by decide)))

theorem fz1_69_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨34, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 34 (by decide)))

theorem fz1_69_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨36, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 36 (by decide)))

theorem fz1_69_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨37, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 37 (by decide)))

theorem fz1_69_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨38, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 38 (by decide)))

theorem fz1_69_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨39, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 39 (by decide)))

theorem fz1_69_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨41, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 41 (by decide)))

theorem fz1_69_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨42, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 42 (by decide)))

theorem fz1_69_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨43, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 43 (by decide)))

theorem fz1_69_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨44, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 44 (by decide)))

theorem fz1_69_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨46, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 46 (by decide)))

theorem fz1_69_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨47, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 47 (by decide)))

theorem fz1_69_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨48, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 48 (by decide)))

theorem fz1_69_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨49, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 49 (by decide)))

theorem fz1_69_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨51, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 51 (by decide)))

theorem fz1_69_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨52, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 52 (by decide)))

theorem fz1_69_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨53, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 53 (by decide)))

theorem fz1_69_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨54, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 54 (by decide)))

theorem fz1_69_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨55, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 55 (by decide)))

theorem fz1_69_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨56, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 56 (by decide)))

theorem fz1_69_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨57, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 57 (by decide)))

theorem fz1_69_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨58, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 58 (by decide)))

theorem fz1_69_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨59, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 59 (by decide)))

theorem fz1_69_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨60, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 60 (by decide)))

theorem fz1_69_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨61, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 61 (by decide)))

theorem fz1_69_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨62, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 62 (by decide)))

theorem fz1_69_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨63, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 63 (by decide)))

theorem fz1_69_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨64, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 64 (by decide)))

theorem fz1_69_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨65, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 65 (by decide)))

theorem fz1_69_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨66, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 66 (by decide)))

theorem fz1_69_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨67, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 67 (by decide)))

theorem fz1_69_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨68, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 68 (by decide)))

theorem fz1_69_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨70, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 70 (by decide)))

theorem fz1_69_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨71, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 71 (by decide)))

theorem fz1_69_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨72, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 72 (by decide)))

theorem fz1_69_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨73, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 73 (by decide)))

theorem fz1_69_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨74, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 74 (by decide)))

theorem fz1_69_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨75, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 75 (by decide)))

theorem fz1_69_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨76, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 76 (by decide)))

theorem fz1_69_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨77, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 77 (by decide)))

theorem fz1_69_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨78, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 78 (by decide)))

theorem fz1_69_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨79, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 79 (by decide)))

theorem fz1_69_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨80, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 80 (by decide)))

theorem fz1_69_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨81, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 81 (by decide)))

theorem fz1_69_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨82, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 82 (by decide)))

theorem fz1_69_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨83, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 83 (by decide)))

theorem fz1_69_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨84, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 84 (by decide)))

theorem fz1_69_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨85, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 85 (by decide)))

theorem fz1_69_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨86, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 86 (by decide)))

theorem fz1_69_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨87, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 87 (by decide)))

theorem fz1_69_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨88, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 88 (by decide)))

theorem fz1_69_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨89, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 89 (by decide)))

theorem fz1_69_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨90, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 90 (by decide)))

theorem fz1_69_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨91, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 91 (by decide)))

theorem fz1_69_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨92, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 92 (by decide)))

theorem fz1_69_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨93, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 93 (by decide)))

theorem fz1_69_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨94, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 94 (by decide)))

theorem fz1_69_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨95, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 95 (by decide)))

theorem fz1_69_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨96, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 96 (by decide)))

theorem fz1_69_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨97, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 97 (by decide)))

theorem fz1_69_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨98, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 98 (by decide)))

theorem fz1_69_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨99, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 99 (by decide)))

theorem fz1_69_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨100, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 100 (by decide)))

theorem fz1_69_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨101, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 101 (by decide)))

theorem fz1_69_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨102, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 102 (by decide)))

theorem fz1_69_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨103, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 103 (by decide)))

theorem fz1_69_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨104, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 104 (by decide)))

theorem fz1_69_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨105, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 105 (by decide)))

theorem fz1_69_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨106, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 106 (by decide)))

theorem fz1_69_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨107, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 107 (by decide)))

theorem fz1_69_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨108, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 108 (by decide)))

theorem fz1_69_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨109, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 109 (by decide)))

theorem fz1_69_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨110, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 110 (by decide)))

theorem fz1_69_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨111, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 111 (by decide)))

theorem fz1_69_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨112, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 112 (by decide)))

theorem fz1_69_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨113, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 113 (by decide)))

theorem fz1_69_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨114, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 114 (by decide)))

theorem fz1_69_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK69)) = 0 :=
  repsFixedCard rK69 ⟨115, by decide⟩ R69 hpxR69 hcardq69
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_69) 115 (by decide)))

theorem fixz2_69 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK69) (retConj 2 (Q2.R69_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_69_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨1, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 1 (by decide)))

theorem fz2_69_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨2, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 2 (by decide)))

theorem fz2_69_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨3, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 3 (by decide)))

theorem fz2_69_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨4, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 4 (by decide)))

theorem fz2_69_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨5, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 5 (by decide)))

theorem fz2_69_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨6, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 6 (by decide)))

theorem fz2_69_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨7, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 7 (by decide)))

theorem fz2_69_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨9, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 9 (by decide)))

theorem fz2_69_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨10, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 10 (by decide)))

theorem fz2_69_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨11, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 11 (by decide)))

theorem fz2_69_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨13, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 13 (by decide)))

theorem fz2_69_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨14, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 14 (by decide)))

theorem fz2_69_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨15, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 15 (by decide)))

theorem fz2_69_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨16, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 16 (by decide)))

theorem fz2_69_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨17, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 17 (by decide)))

theorem fz2_69_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨18, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 18 (by decide)))

theorem fz2_69_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨19, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 19 (by decide)))

theorem fz2_69_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨20, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 20 (by decide)))

theorem fz2_69_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨21, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 21 (by decide)))

theorem fz2_69_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨22, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 22 (by decide)))

theorem fz2_69_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨23, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 23 (by decide)))

theorem fz2_69_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨24, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 24 (by decide)))

theorem fz2_69_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨25, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 25 (by decide)))

theorem fz2_69_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨27, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 27 (by decide)))

theorem fz2_69_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨28, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 28 (by decide)))

theorem fz2_69_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨29, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 29 (by decide)))

theorem fz2_69_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨31, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 31 (by decide)))

theorem fz2_69_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨32, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 32 (by decide)))

theorem fz2_69_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨33, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 33 (by decide)))

theorem fz2_69_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨34, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 34 (by decide)))

theorem fz2_69_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨36, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 36 (by decide)))

theorem fz2_69_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨37, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 37 (by decide)))

theorem fz2_69_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨38, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 38 (by decide)))

theorem fz2_69_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨39, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 39 (by decide)))

theorem fz2_69_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨41, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 41 (by decide)))

theorem fz2_69_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨42, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 42 (by decide)))

theorem fz2_69_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨43, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 43 (by decide)))

theorem fz2_69_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨44, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 44 (by decide)))

theorem fz2_69_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨46, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 46 (by decide)))

theorem fz2_69_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨47, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 47 (by decide)))

theorem fz2_69_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨48, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 48 (by decide)))

theorem fz2_69_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨49, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 49 (by decide)))

theorem fz2_69_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨51, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 51 (by decide)))

theorem fz2_69_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨52, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 52 (by decide)))

theorem fz2_69_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨53, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 53 (by decide)))

theorem fz2_69_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨54, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 54 (by decide)))

theorem fz2_69_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨55, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 55 (by decide)))

theorem fz2_69_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨56, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 56 (by decide)))

theorem fz2_69_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨57, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 57 (by decide)))

theorem fz2_69_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨58, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 58 (by decide)))

theorem fz2_69_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨59, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 59 (by decide)))

theorem fz2_69_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨60, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 60 (by decide)))

theorem fz2_69_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨61, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 61 (by decide)))

theorem fz2_69_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨62, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 62 (by decide)))

theorem fz2_69_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨63, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 63 (by decide)))

theorem fz2_69_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨64, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 64 (by decide)))

theorem fz2_69_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨65, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 65 (by decide)))

theorem fz2_69_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨66, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 66 (by decide)))

theorem fz2_69_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨67, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 67 (by decide)))

theorem fz2_69_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨68, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 68 (by decide)))

theorem fz2_69_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨70, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 70 (by decide)))

theorem fz2_69_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨71, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 71 (by decide)))

theorem fz2_69_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨72, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 72 (by decide)))

theorem fz2_69_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨73, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 73 (by decide)))

theorem fz2_69_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨74, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 74 (by decide)))

theorem fz2_69_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨75, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 75 (by decide)))

theorem fz2_69_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨76, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 76 (by decide)))

theorem fz2_69_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨77, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 77 (by decide)))

theorem fz2_69_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨78, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 78 (by decide)))

theorem fz2_69_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨79, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 79 (by decide)))

theorem fz2_69_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨80, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 80 (by decide)))

theorem fz2_69_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨81, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 81 (by decide)))

theorem fz2_69_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨82, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 82 (by decide)))

theorem fz2_69_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨83, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 83 (by decide)))

theorem fz2_69_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨84, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 84 (by decide)))

theorem fz2_69_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨85, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 85 (by decide)))

theorem fz2_69_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨86, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 86 (by decide)))

theorem fz2_69_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨87, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 87 (by decide)))

theorem fz2_69_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨88, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 88 (by decide)))

theorem fz2_69_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨89, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 89 (by decide)))

theorem fz2_69_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨90, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 90 (by decide)))

theorem fz2_69_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨91, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 91 (by decide)))

theorem fz2_69_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨92, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 92 (by decide)))

theorem fz2_69_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨93, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 93 (by decide)))

theorem fz2_69_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨94, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 94 (by decide)))

theorem fz2_69_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨95, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 95 (by decide)))

theorem fz2_69_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨96, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 96 (by decide)))

theorem fz2_69_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨97, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 97 (by decide)))

theorem fz2_69_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨98, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 98 (by decide)))

theorem fz2_69_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨99, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 99 (by decide)))

theorem fz2_69_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨100, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 100 (by decide)))

theorem fz2_69_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨101, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 101 (by decide)))

theorem fz2_69_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨102, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 102 (by decide)))

theorem fz2_69_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨103, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 103 (by decide)))

theorem fz2_69_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨104, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 104 (by decide)))

theorem fz2_69_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨105, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 105 (by decide)))

theorem fz2_69_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨106, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 106 (by decide)))

theorem fz2_69_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨107, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 107 (by decide)))

theorem fz2_69_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨108, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 108 (by decide)))

theorem fz2_69_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨109, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 109 (by decide)))

theorem fz2_69_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨110, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 110 (by decide)))

theorem fz2_69_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨111, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 111 (by decide)))

theorem fz2_69_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨112, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 112 (by decide)))

theorem fz2_69_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨113, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 113 (by decide)))

theorem fz2_69_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨114, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 114 (by decide)))

theorem fz2_69_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK69)) = 0 :=
  Q2.repsFixedCard2 rK69 ⟨115, by decide⟩ Q2.R69_2 Q2.hpxR69_2 Q2.hcardq69_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_69) 115 (by decide)))

theorem fixz1_70 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK70) (retConj 1 (R70 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_70_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨1, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 1 (by decide)))

theorem fz1_70_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨2, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 2 (by decide)))

theorem fz1_70_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨3, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 3 (by decide)))

theorem fz1_70_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨4, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 4 (by decide)))

theorem fz1_70_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨5, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 5 (by decide)))

theorem fz1_70_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨6, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 6 (by decide)))

theorem fz1_70_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨7, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 7 (by decide)))

theorem fz1_70_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨8, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 8 (by decide)))

theorem fz1_70_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨10, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 10 (by decide)))

theorem fz1_70_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨11, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 11 (by decide)))

theorem fz1_70_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨13, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 13 (by decide)))

theorem fz1_70_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨14, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 14 (by decide)))

theorem fz1_70_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨15, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 15 (by decide)))

theorem fz1_70_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨16, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 16 (by decide)))

theorem fz1_70_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨17, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 17 (by decide)))

theorem fz1_70_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨18, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 18 (by decide)))

theorem fz1_70_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨19, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 19 (by decide)))

theorem fz1_70_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨20, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 20 (by decide)))

theorem fz1_70_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨21, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 21 (by decide)))

theorem fz1_70_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨22, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 22 (by decide)))

theorem fz1_70_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨23, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 23 (by decide)))

theorem fz1_70_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨24, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 24 (by decide)))

theorem fz1_70_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨25, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 25 (by decide)))

theorem fz1_70_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨26, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 26 (by decide)))

theorem fz1_70_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨28, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 28 (by decide)))

theorem fz1_70_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨29, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 29 (by decide)))

theorem fz1_70_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨30, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 30 (by decide)))

theorem fz1_70_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨32, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 32 (by decide)))

theorem fz1_70_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨33, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 33 (by decide)))

theorem fz1_70_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨34, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 34 (by decide)))

theorem fz1_70_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨35, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 35 (by decide)))

theorem fz1_70_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨37, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 37 (by decide)))

theorem fz1_70_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨38, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 38 (by decide)))

theorem fz1_70_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨39, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 39 (by decide)))

theorem fz1_70_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨40, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 40 (by decide)))

theorem fz1_70_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨42, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 42 (by decide)))

theorem fz1_70_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨43, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 43 (by decide)))

theorem fz1_70_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨44, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 44 (by decide)))

theorem fz1_70_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨45, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 45 (by decide)))

theorem fz1_70_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨47, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 47 (by decide)))

theorem fz1_70_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨48, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 48 (by decide)))

theorem fz1_70_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨49, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 49 (by decide)))

theorem fz1_70_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨50, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 50 (by decide)))

theorem fz1_70_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨52, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 52 (by decide)))

theorem fz1_70_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨53, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 53 (by decide)))

theorem fz1_70_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨54, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 54 (by decide)))

theorem fz1_70_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨55, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 55 (by decide)))

theorem fz1_70_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨56, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 56 (by decide)))

theorem fz1_70_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨57, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 57 (by decide)))

theorem fz1_70_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨58, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 58 (by decide)))

theorem fz1_70_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨59, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 59 (by decide)))

theorem fz1_70_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨60, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 60 (by decide)))

theorem fz1_70_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨61, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 61 (by decide)))

theorem fz1_70_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨62, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 62 (by decide)))

theorem fz1_70_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨63, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 63 (by decide)))

theorem fz1_70_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨64, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 64 (by decide)))

theorem fz1_70_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨65, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 65 (by decide)))

theorem fz1_70_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨66, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 66 (by decide)))

theorem fz1_70_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨67, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 67 (by decide)))

theorem fz1_70_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨68, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 68 (by decide)))

theorem fz1_70_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨69, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 69 (by decide)))

theorem fz1_70_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨71, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 71 (by decide)))

theorem fz1_70_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨72, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 72 (by decide)))

theorem fz1_70_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨73, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 73 (by decide)))

theorem fz1_70_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨74, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 74 (by decide)))

theorem fz1_70_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨75, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 75 (by decide)))

theorem fz1_70_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨76, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 76 (by decide)))

theorem fz1_70_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨77, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 77 (by decide)))

theorem fz1_70_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨78, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 78 (by decide)))

theorem fz1_70_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨79, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 79 (by decide)))

theorem fz1_70_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨80, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 80 (by decide)))

theorem fz1_70_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨81, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 81 (by decide)))

theorem fz1_70_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨82, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 82 (by decide)))

theorem fz1_70_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨83, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 83 (by decide)))

theorem fz1_70_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨84, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 84 (by decide)))

theorem fz1_70_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨85, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 85 (by decide)))

theorem fz1_70_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨86, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 86 (by decide)))

theorem fz1_70_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨87, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 87 (by decide)))

theorem fz1_70_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨88, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 88 (by decide)))

theorem fz1_70_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨89, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 89 (by decide)))

theorem fz1_70_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨90, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 90 (by decide)))

theorem fz1_70_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨91, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 91 (by decide)))

theorem fz1_70_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨92, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 92 (by decide)))

theorem fz1_70_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨93, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 93 (by decide)))

theorem fz1_70_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨94, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 94 (by decide)))

theorem fz1_70_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨95, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 95 (by decide)))

theorem fz1_70_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨96, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 96 (by decide)))

theorem fz1_70_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨97, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 97 (by decide)))

theorem fz1_70_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨98, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 98 (by decide)))

theorem fz1_70_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨99, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 99 (by decide)))

theorem fz1_70_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨100, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 100 (by decide)))

theorem fz1_70_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨101, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 101 (by decide)))

theorem fz1_70_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨102, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 102 (by decide)))

theorem fz1_70_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨103, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 103 (by decide)))

theorem fz1_70_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨104, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 104 (by decide)))

theorem fz1_70_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨105, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 105 (by decide)))

theorem fz1_70_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨106, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 106 (by decide)))

theorem fz1_70_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨107, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 107 (by decide)))

theorem fz1_70_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨108, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 108 (by decide)))

theorem fz1_70_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨109, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 109 (by decide)))

theorem fz1_70_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨110, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 110 (by decide)))

theorem fz1_70_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨111, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 111 (by decide)))

theorem fz1_70_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨112, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 112 (by decide)))

theorem fz1_70_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨113, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 113 (by decide)))

theorem fz1_70_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨114, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 114 (by decide)))

theorem fz1_70_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK70)) = 0 :=
  repsFixedCard rK70 ⟨115, by decide⟩ R70 hpxR70 hcardq70
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_70) 115 (by decide)))

theorem fixz2_70 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK70) (retConj 2 (Q2.R70_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_70_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨1, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 1 (by decide)))

theorem fz2_70_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨2, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 2 (by decide)))

theorem fz2_70_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨3, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 3 (by decide)))

theorem fz2_70_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨4, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 4 (by decide)))

theorem fz2_70_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨5, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 5 (by decide)))

theorem fz2_70_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨6, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 6 (by decide)))

theorem fz2_70_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨7, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 7 (by decide)))

theorem fz2_70_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨8, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 8 (by decide)))

theorem fz2_70_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨10, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 10 (by decide)))

theorem fz2_70_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨11, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 11 (by decide)))

theorem fz2_70_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨13, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 13 (by decide)))

theorem fz2_70_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨14, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 14 (by decide)))

theorem fz2_70_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨15, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 15 (by decide)))

theorem fz2_70_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨16, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 16 (by decide)))

theorem fz2_70_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨17, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 17 (by decide)))

theorem fz2_70_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨18, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 18 (by decide)))

theorem fz2_70_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨19, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 19 (by decide)))

theorem fz2_70_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨20, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 20 (by decide)))

theorem fz2_70_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨21, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 21 (by decide)))

theorem fz2_70_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨22, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 22 (by decide)))

theorem fz2_70_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨23, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 23 (by decide)))

theorem fz2_70_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨24, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 24 (by decide)))

theorem fz2_70_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨25, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 25 (by decide)))

theorem fz2_70_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨26, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 26 (by decide)))

theorem fz2_70_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨28, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 28 (by decide)))

theorem fz2_70_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨29, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 29 (by decide)))

theorem fz2_70_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨30, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 30 (by decide)))

theorem fz2_70_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨32, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 32 (by decide)))

theorem fz2_70_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨33, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 33 (by decide)))

theorem fz2_70_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨34, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 34 (by decide)))

theorem fz2_70_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨35, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 35 (by decide)))

theorem fz2_70_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨37, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 37 (by decide)))

theorem fz2_70_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨38, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 38 (by decide)))

theorem fz2_70_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨39, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 39 (by decide)))

theorem fz2_70_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨40, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 40 (by decide)))

theorem fz2_70_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨42, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 42 (by decide)))

theorem fz2_70_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨43, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 43 (by decide)))

theorem fz2_70_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨44, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 44 (by decide)))

theorem fz2_70_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨45, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 45 (by decide)))

theorem fz2_70_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨47, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 47 (by decide)))

theorem fz2_70_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨48, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 48 (by decide)))

theorem fz2_70_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨49, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 49 (by decide)))

theorem fz2_70_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨50, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 50 (by decide)))

theorem fz2_70_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨52, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 52 (by decide)))

theorem fz2_70_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨53, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 53 (by decide)))

theorem fz2_70_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨54, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 54 (by decide)))

theorem fz2_70_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨55, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 55 (by decide)))

theorem fz2_70_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨56, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 56 (by decide)))

theorem fz2_70_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨57, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 57 (by decide)))

theorem fz2_70_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨58, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 58 (by decide)))

theorem fz2_70_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨59, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 59 (by decide)))

theorem fz2_70_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨60, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 60 (by decide)))

theorem fz2_70_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨61, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 61 (by decide)))

theorem fz2_70_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨62, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 62 (by decide)))

theorem fz2_70_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨63, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 63 (by decide)))

theorem fz2_70_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨64, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 64 (by decide)))

theorem fz2_70_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨65, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 65 (by decide)))

theorem fz2_70_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨66, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 66 (by decide)))

theorem fz2_70_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨67, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 67 (by decide)))

theorem fz2_70_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨68, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 68 (by decide)))

theorem fz2_70_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨69, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 69 (by decide)))

theorem fz2_70_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨71, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 71 (by decide)))

theorem fz2_70_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨72, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 72 (by decide)))

theorem fz2_70_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨73, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 73 (by decide)))

theorem fz2_70_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨74, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 74 (by decide)))

theorem fz2_70_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨75, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 75 (by decide)))

theorem fz2_70_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨76, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 76 (by decide)))

theorem fz2_70_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨77, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 77 (by decide)))

theorem fz2_70_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨78, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 78 (by decide)))

theorem fz2_70_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨79, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 79 (by decide)))

theorem fz2_70_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨80, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 80 (by decide)))

theorem fz2_70_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨81, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 81 (by decide)))

theorem fz2_70_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨82, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 82 (by decide)))

theorem fz2_70_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨83, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 83 (by decide)))

theorem fz2_70_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨84, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 84 (by decide)))

theorem fz2_70_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨85, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 85 (by decide)))

theorem fz2_70_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨86, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 86 (by decide)))

theorem fz2_70_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨87, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 87 (by decide)))

theorem fz2_70_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨88, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 88 (by decide)))

theorem fz2_70_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨89, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 89 (by decide)))

theorem fz2_70_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨90, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 90 (by decide)))

theorem fz2_70_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨91, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 91 (by decide)))

theorem fz2_70_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨92, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 92 (by decide)))

theorem fz2_70_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨93, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 93 (by decide)))

theorem fz2_70_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨94, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 94 (by decide)))

theorem fz2_70_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨95, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 95 (by decide)))

theorem fz2_70_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨96, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 96 (by decide)))

theorem fz2_70_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨97, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 97 (by decide)))

theorem fz2_70_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨98, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 98 (by decide)))

theorem fz2_70_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨99, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 99 (by decide)))

theorem fz2_70_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨100, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 100 (by decide)))

theorem fz2_70_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨101, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 101 (by decide)))

theorem fz2_70_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨102, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 102 (by decide)))

theorem fz2_70_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨103, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 103 (by decide)))

theorem fz2_70_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨104, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 104 (by decide)))

theorem fz2_70_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨105, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 105 (by decide)))

theorem fz2_70_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨106, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 106 (by decide)))

theorem fz2_70_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨107, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 107 (by decide)))

theorem fz2_70_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨108, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 108 (by decide)))

theorem fz2_70_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨109, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 109 (by decide)))

theorem fz2_70_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨110, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 110 (by decide)))

theorem fz2_70_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨111, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 111 (by decide)))

theorem fz2_70_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨112, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 112 (by decide)))

theorem fz2_70_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨113, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 113 (by decide)))

theorem fz2_70_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨114, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 114 (by decide)))

theorem fz2_70_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK70)) = 0 :=
  Q2.repsFixedCard2 rK70 ⟨115, by decide⟩ Q2.R70_2 Q2.hpxR70_2 Q2.hcardq70_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_70) 115 (by decide)))

end LeanDring.P5Presentation
