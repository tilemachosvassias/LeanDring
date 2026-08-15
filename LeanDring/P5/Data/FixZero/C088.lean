/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C038
import LeanDring.P5.Data.EntryK.C039
import LeanDring.P5.Data.EntryK.C040
import LeanDring.P5.Data.EntryK.C041
import LeanDring.P5.Data.EntryK.C042
import LeanDring.P5.Data.EntryK.C043

/-!
# Species-table cells, off-support emptiness certificates, chunk 87

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

theorem fixz1_139 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 33, 35, 36, 37, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 97, 98, 99, 101, 102, 103, 104, 105, 106, 108, 109, 110, 111, 112, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK139) (retConj 1 (R139 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_139_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨1, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 1 (by decide)))

theorem fz1_139_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨2, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 2 (by decide)))

theorem fz1_139_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨3, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 3 (by decide)))

theorem fz1_139_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨4, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 4 (by decide)))

theorem fz1_139_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨6, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 6 (by decide)))

theorem fz1_139_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨7, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 7 (by decide)))

theorem fz1_139_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨8, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 8 (by decide)))

theorem fz1_139_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨9, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 9 (by decide)))

theorem fz1_139_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨11, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 11 (by decide)))

theorem fz1_139_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨13, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 13 (by decide)))

theorem fz1_139_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨14, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 14 (by decide)))

theorem fz1_139_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨15, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 15 (by decide)))

theorem fz1_139_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨16, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 16 (by decide)))

theorem fz1_139_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨17, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 17 (by decide)))

theorem fz1_139_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨18, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 18 (by decide)))

theorem fz1_139_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨19, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 19 (by decide)))

theorem fz1_139_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨20, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 20 (by decide)))

theorem fz1_139_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨21, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 21 (by decide)))

theorem fz1_139_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨22, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 22 (by decide)))

theorem fz1_139_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨24, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 24 (by decide)))

theorem fz1_139_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨25, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 25 (by decide)))

theorem fz1_139_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨26, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 26 (by decide)))

theorem fz1_139_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨27, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 27 (by decide)))

theorem fz1_139_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨28, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 28 (by decide)))

theorem fz1_139_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨29, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 29 (by decide)))

theorem fz1_139_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨30, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 30 (by decide)))

theorem fz1_139_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨31, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 31 (by decide)))

theorem fz1_139_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨33, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 33 (by decide)))

theorem fz1_139_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨35, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 35 (by decide)))

theorem fz1_139_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨36, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 36 (by decide)))

theorem fz1_139_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨37, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 37 (by decide)))

theorem fz1_139_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨39, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 39 (by decide)))

theorem fz1_139_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨40, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 40 (by decide)))

theorem fz1_139_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨41, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 41 (by decide)))

theorem fz1_139_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨42, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 42 (by decide)))

theorem fz1_139_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨43, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 43 (by decide)))

theorem fz1_139_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨44, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 44 (by decide)))

theorem fz1_139_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨46, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 46 (by decide)))

theorem fz1_139_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨47, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 47 (by decide)))

theorem fz1_139_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨48, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 48 (by decide)))

theorem fz1_139_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨49, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 49 (by decide)))

theorem fz1_139_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨50, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 50 (by decide)))

theorem fz1_139_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨52, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 52 (by decide)))

theorem fz1_139_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨54, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 54 (by decide)))

theorem fz1_139_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨55, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 55 (by decide)))

theorem fz1_139_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨56, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 56 (by decide)))

theorem fz1_139_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨57, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 57 (by decide)))

theorem fz1_139_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨58, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 58 (by decide)))

theorem fz1_139_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨59, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 59 (by decide)))

theorem fz1_139_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨60, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 60 (by decide)))

theorem fz1_139_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨61, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 61 (by decide)))

theorem fz1_139_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨62, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 62 (by decide)))

theorem fz1_139_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨63, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 63 (by decide)))

theorem fz1_139_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨64, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 64 (by decide)))

theorem fz1_139_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨65, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 65 (by decide)))

theorem fz1_139_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨66, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 66 (by decide)))

theorem fz1_139_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨67, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 67 (by decide)))

theorem fz1_139_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨68, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 68 (by decide)))

theorem fz1_139_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨69, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 69 (by decide)))

theorem fz1_139_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨70, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 70 (by decide)))

theorem fz1_139_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨71, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 71 (by decide)))

theorem fz1_139_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨72, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 72 (by decide)))

theorem fz1_139_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨73, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 73 (by decide)))

theorem fz1_139_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨74, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 74 (by decide)))

theorem fz1_139_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨75, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 75 (by decide)))

theorem fz1_139_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨76, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 76 (by decide)))

theorem fz1_139_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨77, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 77 (by decide)))

theorem fz1_139_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨78, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 78 (by decide)))

theorem fz1_139_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨79, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 79 (by decide)))

theorem fz1_139_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨80, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 80 (by decide)))

theorem fz1_139_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨81, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 81 (by decide)))

theorem fz1_139_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨82, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 82 (by decide)))

theorem fz1_139_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨83, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 83 (by decide)))

theorem fz1_139_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨85, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 85 (by decide)))

theorem fz1_139_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨86, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 86 (by decide)))

theorem fz1_139_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨87, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 87 (by decide)))

theorem fz1_139_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨88, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 88 (by decide)))

theorem fz1_139_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨89, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 89 (by decide)))

theorem fz1_139_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨90, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 90 (by decide)))

theorem fz1_139_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨91, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 91 (by decide)))

theorem fz1_139_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨92, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 92 (by decide)))

theorem fz1_139_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨93, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 93 (by decide)))

theorem fz1_139_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨95, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 95 (by decide)))

theorem fz1_139_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨97, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 97 (by decide)))

theorem fz1_139_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨98, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 98 (by decide)))

theorem fz1_139_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨99, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 99 (by decide)))

theorem fz1_139_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨101, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 101 (by decide)))

theorem fz1_139_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨102, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 102 (by decide)))

theorem fz1_139_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨103, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 103 (by decide)))

theorem fz1_139_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨104, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 104 (by decide)))

theorem fz1_139_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨105, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 105 (by decide)))

theorem fz1_139_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨106, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 106 (by decide)))

theorem fz1_139_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨108, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 108 (by decide)))

theorem fz1_139_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨109, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 109 (by decide)))

theorem fz1_139_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨110, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 110 (by decide)))

theorem fz1_139_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨111, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 111 (by decide)))

theorem fz1_139_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨112, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 112 (by decide)))

theorem fz1_139_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨114, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 114 (by decide)))

theorem fz1_139_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨115, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 115 (by decide)))

theorem fz1_139_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨116, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 116 (by decide)))

theorem fz1_139_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨117, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 117 (by decide)))

theorem fz1_139_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨118, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 118 (by decide)))

theorem fz1_139_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨119, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 119 (by decide)))

theorem fz1_139_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨120, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 120 (by decide)))

theorem fz1_139_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨121, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 121 (by decide)))

theorem fz1_139_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨122, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 122 (by decide)))

theorem fz1_139_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨123, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 123 (by decide)))

theorem fz1_139_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨124, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 124 (by decide)))

theorem fz1_139_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨125, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 125 (by decide)))

theorem fz1_139_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨126, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 126 (by decide)))

theorem fz1_139_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨127, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 127 (by decide)))

theorem fz1_139_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨128, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 128 (by decide)))

theorem fz1_139_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨129, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 129 (by decide)))

theorem fz1_139_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨130, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 130 (by decide)))

theorem fz1_139_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨131, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 131 (by decide)))

theorem fz1_139_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨132, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 132 (by decide)))

theorem fz1_139_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨133, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 133 (by decide)))

theorem fz1_139_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨134, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 134 (by decide)))

theorem fz1_139_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨135, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 135 (by decide)))

theorem fz1_139_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨136, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 136 (by decide)))

theorem fz1_139_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨137, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 137 (by decide)))

theorem fz1_139_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨138, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 138 (by decide)))

theorem fz1_139_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨140, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 140 (by decide)))

theorem fz1_139_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨141, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 141 (by decide)))

theorem fz1_139_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨142, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 142 (by decide)))

theorem fz1_139_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨143, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 143 (by decide)))

theorem fz1_139_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨144, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 144 (by decide)))

theorem fz1_139_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨145, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 145 (by decide)))

theorem fz1_139_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK139)) = 0 :=
  repsFixedCard rK139 ⟨146, by decide⟩ R139 hpxR139 hcardq139
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_139) 146 (by decide)))

theorem fixz2_139 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 33, 35, 36, 37, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 97, 98, 99, 101, 102, 103, 104, 105, 106, 108, 109, 110, 111, 112, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK139) (retConj 2 (Q2.R139_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_139_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨1, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 1 (by decide)))

theorem fz2_139_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨2, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 2 (by decide)))

theorem fz2_139_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨3, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 3 (by decide)))

theorem fz2_139_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨4, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 4 (by decide)))

theorem fz2_139_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨6, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 6 (by decide)))

theorem fz2_139_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨7, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 7 (by decide)))

theorem fz2_139_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨8, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 8 (by decide)))

theorem fz2_139_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨9, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 9 (by decide)))

theorem fz2_139_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨11, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 11 (by decide)))

theorem fz2_139_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨13, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 13 (by decide)))

theorem fz2_139_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨14, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 14 (by decide)))

theorem fz2_139_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨15, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 15 (by decide)))

theorem fz2_139_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨16, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 16 (by decide)))

theorem fz2_139_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨17, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 17 (by decide)))

theorem fz2_139_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨18, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 18 (by decide)))

theorem fz2_139_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨19, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 19 (by decide)))

theorem fz2_139_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨20, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 20 (by decide)))

theorem fz2_139_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨21, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 21 (by decide)))

theorem fz2_139_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨22, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 22 (by decide)))

theorem fz2_139_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨24, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 24 (by decide)))

theorem fz2_139_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨25, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 25 (by decide)))

theorem fz2_139_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨26, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 26 (by decide)))

theorem fz2_139_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨27, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 27 (by decide)))

theorem fz2_139_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨28, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 28 (by decide)))

theorem fz2_139_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨29, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 29 (by decide)))

theorem fz2_139_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨30, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 30 (by decide)))

theorem fz2_139_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨31, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 31 (by decide)))

theorem fz2_139_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨33, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 33 (by decide)))

theorem fz2_139_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨35, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 35 (by decide)))

theorem fz2_139_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨36, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 36 (by decide)))

theorem fz2_139_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨37, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 37 (by decide)))

theorem fz2_139_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨39, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 39 (by decide)))

theorem fz2_139_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨40, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 40 (by decide)))

theorem fz2_139_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨41, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 41 (by decide)))

theorem fz2_139_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨42, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 42 (by decide)))

theorem fz2_139_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨43, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 43 (by decide)))

theorem fz2_139_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨44, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 44 (by decide)))

theorem fz2_139_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨46, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 46 (by decide)))

theorem fz2_139_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨47, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 47 (by decide)))

theorem fz2_139_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨48, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 48 (by decide)))

theorem fz2_139_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨49, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 49 (by decide)))

theorem fz2_139_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨50, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 50 (by decide)))

theorem fz2_139_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨52, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 52 (by decide)))

theorem fz2_139_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨54, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 54 (by decide)))

theorem fz2_139_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨55, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 55 (by decide)))

theorem fz2_139_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨56, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 56 (by decide)))

theorem fz2_139_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨57, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 57 (by decide)))

theorem fz2_139_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨58, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 58 (by decide)))

theorem fz2_139_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨59, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 59 (by decide)))

theorem fz2_139_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨60, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 60 (by decide)))

theorem fz2_139_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨61, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 61 (by decide)))

theorem fz2_139_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨62, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 62 (by decide)))

theorem fz2_139_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨63, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 63 (by decide)))

theorem fz2_139_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨64, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 64 (by decide)))

theorem fz2_139_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨65, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 65 (by decide)))

theorem fz2_139_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨66, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 66 (by decide)))

theorem fz2_139_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨67, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 67 (by decide)))

theorem fz2_139_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨68, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 68 (by decide)))

theorem fz2_139_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨69, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 69 (by decide)))

theorem fz2_139_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨70, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 70 (by decide)))

theorem fz2_139_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨71, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 71 (by decide)))

theorem fz2_139_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨72, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 72 (by decide)))

theorem fz2_139_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨73, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 73 (by decide)))

theorem fz2_139_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨74, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 74 (by decide)))

theorem fz2_139_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨75, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 75 (by decide)))

theorem fz2_139_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨76, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 76 (by decide)))

theorem fz2_139_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨77, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 77 (by decide)))

theorem fz2_139_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨78, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 78 (by decide)))

theorem fz2_139_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨79, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 79 (by decide)))

theorem fz2_139_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨80, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 80 (by decide)))

theorem fz2_139_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨81, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 81 (by decide)))

theorem fz2_139_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨82, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 82 (by decide)))

theorem fz2_139_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨83, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 83 (by decide)))

theorem fz2_139_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨85, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 85 (by decide)))

theorem fz2_139_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨86, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 86 (by decide)))

theorem fz2_139_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨87, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 87 (by decide)))

theorem fz2_139_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨88, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 88 (by decide)))

theorem fz2_139_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨89, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 89 (by decide)))

theorem fz2_139_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨90, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 90 (by decide)))

theorem fz2_139_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨91, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 91 (by decide)))

theorem fz2_139_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨92, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 92 (by decide)))

theorem fz2_139_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨93, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 93 (by decide)))

theorem fz2_139_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨95, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 95 (by decide)))

theorem fz2_139_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨97, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 97 (by decide)))

theorem fz2_139_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨98, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 98 (by decide)))

theorem fz2_139_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨99, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 99 (by decide)))

theorem fz2_139_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨101, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 101 (by decide)))

theorem fz2_139_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨102, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 102 (by decide)))

theorem fz2_139_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨103, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 103 (by decide)))

theorem fz2_139_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨104, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 104 (by decide)))

theorem fz2_139_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨105, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 105 (by decide)))

theorem fz2_139_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨106, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 106 (by decide)))

theorem fz2_139_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨108, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 108 (by decide)))

theorem fz2_139_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨109, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 109 (by decide)))

theorem fz2_139_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨110, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 110 (by decide)))

theorem fz2_139_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨111, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 111 (by decide)))

theorem fz2_139_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨112, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 112 (by decide)))

theorem fz2_139_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨114, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 114 (by decide)))

theorem fz2_139_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨115, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 115 (by decide)))

theorem fz2_139_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨116, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 116 (by decide)))

theorem fz2_139_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨117, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 117 (by decide)))

theorem fz2_139_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨118, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 118 (by decide)))

theorem fz2_139_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨119, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 119 (by decide)))

theorem fz2_139_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨120, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 120 (by decide)))

theorem fz2_139_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨121, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 121 (by decide)))

theorem fz2_139_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨122, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 122 (by decide)))

theorem fz2_139_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨123, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 123 (by decide)))

theorem fz2_139_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨124, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 124 (by decide)))

theorem fz2_139_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨125, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 125 (by decide)))

theorem fz2_139_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨126, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 126 (by decide)))

theorem fz2_139_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨127, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 127 (by decide)))

theorem fz2_139_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨128, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 128 (by decide)))

theorem fz2_139_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨129, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 129 (by decide)))

theorem fz2_139_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨130, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 130 (by decide)))

theorem fz2_139_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨131, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 131 (by decide)))

theorem fz2_139_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨132, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 132 (by decide)))

theorem fz2_139_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨133, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 133 (by decide)))

theorem fz2_139_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨134, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 134 (by decide)))

theorem fz2_139_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨135, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 135 (by decide)))

theorem fz2_139_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨136, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 136 (by decide)))

theorem fz2_139_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨137, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 137 (by decide)))

theorem fz2_139_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨138, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 138 (by decide)))

theorem fz2_139_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨140, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 140 (by decide)))

theorem fz2_139_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨141, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 141 (by decide)))

theorem fz2_139_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨142, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 142 (by decide)))

theorem fz2_139_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨143, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 143 (by decide)))

theorem fz2_139_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨144, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 144 (by decide)))

theorem fz2_139_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨145, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 145 (by decide)))

theorem fz2_139_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK139)) = 0 :=
  Q2.repsFixedCard2 rK139 ⟨146, by decide⟩ Q2.R139_2 Q2.hpxR139_2 Q2.hcardq139_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_139) 146 (by decide)))

theorem fixz1_140 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 41, 42, 43, 44, 45, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 91, 92, 93, 94, 95, 96, 98, 99, 100, 102, 103, 104, 105, 106, 107, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK140) (retConj 1 (R140 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_140_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨1, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 1 (by decide)))

theorem fz1_140_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨2, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 2 (by decide)))

theorem fz1_140_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨3, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 3 (by decide)))

theorem fz1_140_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨4, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 4 (by decide)))

theorem fz1_140_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨6, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 6 (by decide)))

theorem fz1_140_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨7, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 7 (by decide)))

theorem fz1_140_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨8, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 8 (by decide)))

theorem fz1_140_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨9, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 9 (by decide)))

theorem fz1_140_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨11, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 11 (by decide)))

theorem fz1_140_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨13, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 13 (by decide)))

theorem fz1_140_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨14, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 14 (by decide)))

theorem fz1_140_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨15, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 15 (by decide)))

theorem fz1_140_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨16, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 16 (by decide)))

theorem fz1_140_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨17, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 17 (by decide)))

theorem fz1_140_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨18, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 18 (by decide)))

theorem fz1_140_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨19, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 19 (by decide)))

theorem fz1_140_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨20, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 20 (by decide)))

theorem fz1_140_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨21, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 21 (by decide)))

theorem fz1_140_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨22, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 22 (by decide)))

theorem fz1_140_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨24, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 24 (by decide)))

theorem fz1_140_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨25, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 25 (by decide)))

theorem fz1_140_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨26, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 26 (by decide)))

theorem fz1_140_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨27, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 27 (by decide)))

theorem fz1_140_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨29, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 29 (by decide)))

theorem fz1_140_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨30, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 30 (by decide)))

theorem fz1_140_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨31, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 31 (by decide)))

theorem fz1_140_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨32, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 32 (by decide)))

theorem fz1_140_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨33, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 33 (by decide)))

theorem fz1_140_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨34, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 34 (by decide)))

theorem fz1_140_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨36, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 36 (by decide)))

theorem fz1_140_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨37, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 37 (by decide)))

theorem fz1_140_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨38, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 38 (by decide)))

theorem fz1_140_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨40, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 40 (by decide)))

theorem fz1_140_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨41, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 41 (by decide)))

theorem fz1_140_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨42, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 42 (by decide)))

theorem fz1_140_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨43, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 43 (by decide)))

theorem fz1_140_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨44, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 44 (by decide)))

theorem fz1_140_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨45, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 45 (by decide)))

theorem fz1_140_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨47, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 47 (by decide)))

theorem fz1_140_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨48, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 48 (by decide)))

theorem fz1_140_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨49, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 49 (by decide)))

theorem fz1_140_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨50, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 50 (by decide)))

theorem fz1_140_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨51, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 51 (by decide)))

theorem fz1_140_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨54, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 54 (by decide)))

theorem fz1_140_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨55, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 55 (by decide)))

theorem fz1_140_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨56, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 56 (by decide)))

theorem fz1_140_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨57, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 57 (by decide)))

theorem fz1_140_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨58, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 58 (by decide)))

theorem fz1_140_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨59, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 59 (by decide)))

theorem fz1_140_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨60, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 60 (by decide)))

theorem fz1_140_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨61, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 61 (by decide)))

theorem fz1_140_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨62, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 62 (by decide)))

theorem fz1_140_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨63, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 63 (by decide)))

theorem fz1_140_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨64, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 64 (by decide)))

theorem fz1_140_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨65, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 65 (by decide)))

theorem fz1_140_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨66, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 66 (by decide)))

theorem fz1_140_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨67, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 67 (by decide)))

theorem fz1_140_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨68, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 68 (by decide)))

theorem fz1_140_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨69, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 69 (by decide)))

theorem fz1_140_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨70, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 70 (by decide)))

theorem fz1_140_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨71, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 71 (by decide)))

theorem fz1_140_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨72, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 72 (by decide)))

theorem fz1_140_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨73, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 73 (by decide)))

theorem fz1_140_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨74, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 74 (by decide)))

theorem fz1_140_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨75, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 75 (by decide)))

theorem fz1_140_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨76, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 76 (by decide)))

theorem fz1_140_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨77, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 77 (by decide)))

theorem fz1_140_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨78, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 78 (by decide)))

theorem fz1_140_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨79, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 79 (by decide)))

theorem fz1_140_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨80, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 80 (by decide)))

theorem fz1_140_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨81, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 81 (by decide)))

theorem fz1_140_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨82, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 82 (by decide)))

theorem fz1_140_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨83, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 83 (by decide)))

theorem fz1_140_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨85, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 85 (by decide)))

theorem fz1_140_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨86, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 86 (by decide)))

theorem fz1_140_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨87, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 87 (by decide)))

theorem fz1_140_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨88, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 88 (by decide)))

theorem fz1_140_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨89, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 89 (by decide)))

theorem fz1_140_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨91, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 91 (by decide)))

theorem fz1_140_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨92, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 92 (by decide)))

theorem fz1_140_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨93, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 93 (by decide)))

theorem fz1_140_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨94, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 94 (by decide)))

theorem fz1_140_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨95, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 95 (by decide)))

theorem fz1_140_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨96, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 96 (by decide)))

theorem fz1_140_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨98, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 98 (by decide)))

theorem fz1_140_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨99, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 99 (by decide)))

theorem fz1_140_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨100, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 100 (by decide)))

theorem fz1_140_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨102, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 102 (by decide)))

theorem fz1_140_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨103, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 103 (by decide)))

theorem fz1_140_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨104, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 104 (by decide)))

theorem fz1_140_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨105, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 105 (by decide)))

theorem fz1_140_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨106, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 106 (by decide)))

theorem fz1_140_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨107, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 107 (by decide)))

theorem fz1_140_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨109, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 109 (by decide)))

theorem fz1_140_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨110, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 110 (by decide)))

theorem fz1_140_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨111, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 111 (by decide)))

theorem fz1_140_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨112, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 112 (by decide)))

theorem fz1_140_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨113, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 113 (by decide)))

theorem fz1_140_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨115, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 115 (by decide)))

theorem fz1_140_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨116, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 116 (by decide)))

theorem fz1_140_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨117, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 117 (by decide)))

theorem fz1_140_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨118, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 118 (by decide)))

theorem fz1_140_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨119, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 119 (by decide)))

theorem fz1_140_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨120, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 120 (by decide)))

theorem fz1_140_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨121, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 121 (by decide)))

theorem fz1_140_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨122, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 122 (by decide)))

theorem fz1_140_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨123, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 123 (by decide)))

theorem fz1_140_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨124, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 124 (by decide)))

theorem fz1_140_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨125, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 125 (by decide)))

theorem fz1_140_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨126, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 126 (by decide)))

theorem fz1_140_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨127, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 127 (by decide)))

theorem fz1_140_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨128, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 128 (by decide)))

theorem fz1_140_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨129, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 129 (by decide)))

theorem fz1_140_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨130, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 130 (by decide)))

theorem fz1_140_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨131, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 131 (by decide)))

theorem fz1_140_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨132, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 132 (by decide)))

theorem fz1_140_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨133, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 133 (by decide)))

theorem fz1_140_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨134, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 134 (by decide)))

theorem fz1_140_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨135, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 135 (by decide)))

theorem fz1_140_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨136, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 136 (by decide)))

theorem fz1_140_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨137, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 137 (by decide)))

theorem fz1_140_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨138, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 138 (by decide)))

theorem fz1_140_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨139, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 139 (by decide)))

theorem fz1_140_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨141, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 141 (by decide)))

theorem fz1_140_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨142, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 142 (by decide)))

theorem fz1_140_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨143, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 143 (by decide)))

theorem fz1_140_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨144, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 144 (by decide)))

theorem fz1_140_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨145, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 145 (by decide)))

theorem fz1_140_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK140)) = 0 :=
  repsFixedCard rK140 ⟨146, by decide⟩ R140 hpxR140 hcardq140
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_140) 146 (by decide)))

theorem fixz2_140 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 41, 42, 43, 44, 45, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 91, 92, 93, 94, 95, 96, 98, 99, 100, 102, 103, 104, 105, 106, 107, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK140) (retConj 2 (Q2.R140_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_140_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨1, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 1 (by decide)))

theorem fz2_140_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨2, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 2 (by decide)))

theorem fz2_140_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨3, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 3 (by decide)))

theorem fz2_140_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨4, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 4 (by decide)))

theorem fz2_140_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨6, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 6 (by decide)))

theorem fz2_140_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨7, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 7 (by decide)))

theorem fz2_140_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨8, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 8 (by decide)))

theorem fz2_140_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨9, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 9 (by decide)))

theorem fz2_140_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨11, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 11 (by decide)))

theorem fz2_140_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨13, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 13 (by decide)))

theorem fz2_140_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨14, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 14 (by decide)))

theorem fz2_140_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨15, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 15 (by decide)))

theorem fz2_140_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨16, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 16 (by decide)))

theorem fz2_140_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨17, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 17 (by decide)))

theorem fz2_140_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨18, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 18 (by decide)))

theorem fz2_140_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨19, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 19 (by decide)))

theorem fz2_140_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨20, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 20 (by decide)))

theorem fz2_140_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨21, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 21 (by decide)))

theorem fz2_140_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨22, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 22 (by decide)))

theorem fz2_140_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨24, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 24 (by decide)))

theorem fz2_140_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨25, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 25 (by decide)))

theorem fz2_140_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨26, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 26 (by decide)))

theorem fz2_140_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨27, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 27 (by decide)))

theorem fz2_140_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨29, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 29 (by decide)))

theorem fz2_140_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨30, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 30 (by decide)))

theorem fz2_140_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨31, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 31 (by decide)))

theorem fz2_140_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨32, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 32 (by decide)))

theorem fz2_140_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨33, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 33 (by decide)))

theorem fz2_140_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨34, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 34 (by decide)))

theorem fz2_140_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨36, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 36 (by decide)))

theorem fz2_140_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨37, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 37 (by decide)))

theorem fz2_140_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨38, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 38 (by decide)))

theorem fz2_140_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨40, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 40 (by decide)))

theorem fz2_140_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨41, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 41 (by decide)))

theorem fz2_140_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨42, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 42 (by decide)))

theorem fz2_140_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨43, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 43 (by decide)))

theorem fz2_140_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨44, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 44 (by decide)))

theorem fz2_140_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨45, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 45 (by decide)))

theorem fz2_140_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨47, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 47 (by decide)))

theorem fz2_140_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨48, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 48 (by decide)))

theorem fz2_140_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨49, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 49 (by decide)))

theorem fz2_140_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨50, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 50 (by decide)))

theorem fz2_140_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨51, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 51 (by decide)))

theorem fz2_140_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨54, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 54 (by decide)))

theorem fz2_140_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨55, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 55 (by decide)))

theorem fz2_140_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨56, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 56 (by decide)))

theorem fz2_140_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨57, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 57 (by decide)))

theorem fz2_140_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨58, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 58 (by decide)))

theorem fz2_140_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨59, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 59 (by decide)))

theorem fz2_140_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨60, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 60 (by decide)))

theorem fz2_140_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨61, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 61 (by decide)))

theorem fz2_140_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨62, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 62 (by decide)))

theorem fz2_140_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨63, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 63 (by decide)))

theorem fz2_140_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨64, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 64 (by decide)))

theorem fz2_140_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨65, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 65 (by decide)))

theorem fz2_140_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨66, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 66 (by decide)))

theorem fz2_140_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨67, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 67 (by decide)))

theorem fz2_140_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨68, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 68 (by decide)))

theorem fz2_140_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨69, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 69 (by decide)))

theorem fz2_140_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨70, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 70 (by decide)))

theorem fz2_140_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨71, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 71 (by decide)))

theorem fz2_140_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨72, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 72 (by decide)))

theorem fz2_140_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨73, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 73 (by decide)))

theorem fz2_140_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨74, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 74 (by decide)))

theorem fz2_140_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨75, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 75 (by decide)))

theorem fz2_140_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨76, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 76 (by decide)))

theorem fz2_140_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨77, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 77 (by decide)))

theorem fz2_140_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨78, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 78 (by decide)))

theorem fz2_140_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨79, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 79 (by decide)))

theorem fz2_140_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨80, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 80 (by decide)))

theorem fz2_140_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨81, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 81 (by decide)))

theorem fz2_140_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨82, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 82 (by decide)))

theorem fz2_140_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨83, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 83 (by decide)))

theorem fz2_140_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨85, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 85 (by decide)))

theorem fz2_140_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨86, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 86 (by decide)))

theorem fz2_140_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨87, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 87 (by decide)))

theorem fz2_140_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨88, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 88 (by decide)))

theorem fz2_140_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨89, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 89 (by decide)))

theorem fz2_140_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨91, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 91 (by decide)))

theorem fz2_140_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨92, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 92 (by decide)))

theorem fz2_140_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨93, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 93 (by decide)))

theorem fz2_140_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨94, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 94 (by decide)))

theorem fz2_140_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨95, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 95 (by decide)))

theorem fz2_140_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨96, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 96 (by decide)))

theorem fz2_140_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨98, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 98 (by decide)))

theorem fz2_140_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨99, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 99 (by decide)))

theorem fz2_140_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨100, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 100 (by decide)))

theorem fz2_140_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨102, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 102 (by decide)))

theorem fz2_140_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨103, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 103 (by decide)))

theorem fz2_140_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨104, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 104 (by decide)))

theorem fz2_140_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨105, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 105 (by decide)))

theorem fz2_140_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨106, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 106 (by decide)))

theorem fz2_140_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨107, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 107 (by decide)))

theorem fz2_140_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨109, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 109 (by decide)))

theorem fz2_140_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨110, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 110 (by decide)))

theorem fz2_140_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨111, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 111 (by decide)))

theorem fz2_140_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨112, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 112 (by decide)))

theorem fz2_140_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨113, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 113 (by decide)))

theorem fz2_140_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨115, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 115 (by decide)))

theorem fz2_140_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨116, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 116 (by decide)))

theorem fz2_140_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨117, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 117 (by decide)))

theorem fz2_140_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨118, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 118 (by decide)))

theorem fz2_140_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨119, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 119 (by decide)))

theorem fz2_140_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨120, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 120 (by decide)))

theorem fz2_140_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨121, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 121 (by decide)))

theorem fz2_140_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨122, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 122 (by decide)))

theorem fz2_140_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨123, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 123 (by decide)))

theorem fz2_140_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨124, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 124 (by decide)))

theorem fz2_140_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨125, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 125 (by decide)))

theorem fz2_140_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨126, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 126 (by decide)))

theorem fz2_140_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨127, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 127 (by decide)))

theorem fz2_140_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨128, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 128 (by decide)))

theorem fz2_140_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨129, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 129 (by decide)))

theorem fz2_140_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨130, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 130 (by decide)))

theorem fz2_140_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨131, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 131 (by decide)))

theorem fz2_140_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨132, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 132 (by decide)))

theorem fz2_140_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨133, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 133 (by decide)))

theorem fz2_140_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨134, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 134 (by decide)))

theorem fz2_140_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨135, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 135 (by decide)))

theorem fz2_140_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨136, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 136 (by decide)))

theorem fz2_140_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨137, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 137 (by decide)))

theorem fz2_140_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨138, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 138 (by decide)))

theorem fz2_140_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨139, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 139 (by decide)))

theorem fz2_140_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨141, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 141 (by decide)))

theorem fz2_140_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨142, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 142 (by decide)))

theorem fz2_140_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨143, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 143 (by decide)))

theorem fz2_140_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨144, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 144 (by decide)))

theorem fz2_140_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨145, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 145 (by decide)))

theorem fz2_140_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK140)) = 0 :=
  Q2.repsFixedCard2 rK140 ⟨146, by decide⟩ Q2.R140_2 Q2.hpxR140_2 Q2.hcardq140_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_140) 146 (by decide)))

theorem fixz1_141 : ([28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK141) (retConj 1 (R141 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_141_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨28, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 28 (by decide)))

theorem fz1_141_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨29, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 29 (by decide)))

theorem fz1_141_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨30, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 30 (by decide)))

theorem fz1_141_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨31, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 31 (by decide)))

theorem fz1_141_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨32, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 32 (by decide)))

theorem fz1_141_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨33, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 33 (by decide)))

theorem fz1_141_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨34, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 34 (by decide)))

theorem fz1_141_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨35, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 35 (by decide)))

theorem fz1_141_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨36, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 36 (by decide)))

theorem fz1_141_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨37, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 37 (by decide)))

theorem fz1_141_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨38, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 38 (by decide)))

theorem fz1_141_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨39, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 39 (by decide)))

theorem fz1_141_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨40, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 40 (by decide)))

theorem fz1_141_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨41, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 41 (by decide)))

theorem fz1_141_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨42, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 42 (by decide)))

theorem fz1_141_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨43, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 43 (by decide)))

theorem fz1_141_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨44, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 44 (by decide)))

theorem fz1_141_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨45, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 45 (by decide)))

theorem fz1_141_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨46, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 46 (by decide)))

theorem fz1_141_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨47, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 47 (by decide)))

theorem fz1_141_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨48, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 48 (by decide)))

theorem fz1_141_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨49, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 49 (by decide)))

theorem fz1_141_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨50, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 50 (by decide)))

theorem fz1_141_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨51, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 51 (by decide)))

theorem fz1_141_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨52, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 52 (by decide)))

theorem fz1_141_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨55, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 55 (by decide)))

theorem fz1_141_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨56, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 56 (by decide)))

theorem fz1_141_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨57, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 57 (by decide)))

theorem fz1_141_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨58, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 58 (by decide)))

theorem fz1_141_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨59, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 59 (by decide)))

theorem fz1_141_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨60, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 60 (by decide)))

theorem fz1_141_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨61, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 61 (by decide)))

theorem fz1_141_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨62, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 62 (by decide)))

theorem fz1_141_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨63, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 63 (by decide)))

theorem fz1_141_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨64, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 64 (by decide)))

theorem fz1_141_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨65, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 65 (by decide)))

theorem fz1_141_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨66, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 66 (by decide)))

theorem fz1_141_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨67, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 67 (by decide)))

theorem fz1_141_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨68, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 68 (by decide)))

theorem fz1_141_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨69, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 69 (by decide)))

theorem fz1_141_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨70, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 70 (by decide)))

theorem fz1_141_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨71, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 71 (by decide)))

theorem fz1_141_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨72, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 72 (by decide)))

theorem fz1_141_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨73, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 73 (by decide)))

theorem fz1_141_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨74, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 74 (by decide)))

theorem fz1_141_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨75, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 75 (by decide)))

theorem fz1_141_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨76, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 76 (by decide)))

theorem fz1_141_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨77, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 77 (by decide)))

theorem fz1_141_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨78, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 78 (by decide)))

theorem fz1_141_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨79, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 79 (by decide)))

theorem fz1_141_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨90, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 90 (by decide)))

theorem fz1_141_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨91, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 91 (by decide)))

theorem fz1_141_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨92, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 92 (by decide)))

theorem fz1_141_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨93, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 93 (by decide)))

theorem fz1_141_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨94, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 94 (by decide)))

theorem fz1_141_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨95, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 95 (by decide)))

theorem fz1_141_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨96, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 96 (by decide)))

theorem fz1_141_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨97, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 97 (by decide)))

theorem fz1_141_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨98, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 98 (by decide)))

theorem fz1_141_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨99, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 99 (by decide)))

theorem fz1_141_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨100, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 100 (by decide)))

theorem fz1_141_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨101, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 101 (by decide)))

theorem fz1_141_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨102, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 102 (by decide)))

theorem fz1_141_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨103, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 103 (by decide)))

theorem fz1_141_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨104, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 104 (by decide)))

theorem fz1_141_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨105, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 105 (by decide)))

theorem fz1_141_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨106, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 106 (by decide)))

theorem fz1_141_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨107, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 107 (by decide)))

theorem fz1_141_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨108, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 108 (by decide)))

theorem fz1_141_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨109, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 109 (by decide)))

theorem fz1_141_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨110, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 110 (by decide)))

theorem fz1_141_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨111, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 111 (by decide)))

theorem fz1_141_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨112, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 112 (by decide)))

theorem fz1_141_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨113, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 113 (by decide)))

theorem fz1_141_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨114, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 114 (by decide)))

theorem fz1_141_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨116, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 116 (by decide)))

theorem fz1_141_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨117, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 117 (by decide)))

theorem fz1_141_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨118, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 118 (by decide)))

theorem fz1_141_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨119, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 119 (by decide)))

theorem fz1_141_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨120, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 120 (by decide)))

theorem fz1_141_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨121, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 121 (by decide)))

theorem fz1_141_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨122, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 122 (by decide)))

theorem fz1_141_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨123, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 123 (by decide)))

theorem fz1_141_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨124, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 124 (by decide)))

theorem fz1_141_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨125, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 125 (by decide)))

theorem fz1_141_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨126, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 126 (by decide)))

theorem fz1_141_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨127, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 127 (by decide)))

theorem fz1_141_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨128, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 128 (by decide)))

theorem fz1_141_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨129, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 129 (by decide)))

theorem fz1_141_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨130, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 130 (by decide)))

theorem fz1_141_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨131, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 131 (by decide)))

theorem fz1_141_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨132, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 132 (by decide)))

theorem fz1_141_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨133, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 133 (by decide)))

theorem fz1_141_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨134, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 134 (by decide)))

theorem fz1_141_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨135, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 135 (by decide)))

theorem fz1_141_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨136, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 136 (by decide)))

theorem fz1_141_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨137, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 137 (by decide)))

theorem fz1_141_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨138, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 138 (by decide)))

theorem fz1_141_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨139, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 139 (by decide)))

theorem fz1_141_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨140, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 140 (by decide)))

theorem fz1_141_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨142, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 142 (by decide)))

theorem fz1_141_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨143, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 143 (by decide)))

theorem fz1_141_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨144, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 144 (by decide)))

theorem fz1_141_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨145, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 145 (by decide)))

theorem fz1_141_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK141)) = 0 :=
  repsFixedCard rK141 ⟨146, by decide⟩ R141 hpxR141 hcardq141
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_141) 146 (by decide)))

theorem fixz2_141 : ([28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK141) (retConj 2 (Q2.R141_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_141_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨28, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 28 (by decide)))

theorem fz2_141_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨29, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 29 (by decide)))

theorem fz2_141_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨30, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 30 (by decide)))

theorem fz2_141_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨31, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 31 (by decide)))

theorem fz2_141_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨32, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 32 (by decide)))

theorem fz2_141_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨33, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 33 (by decide)))

theorem fz2_141_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨34, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 34 (by decide)))

theorem fz2_141_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨35, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 35 (by decide)))

theorem fz2_141_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨36, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 36 (by decide)))

theorem fz2_141_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨37, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 37 (by decide)))

theorem fz2_141_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨38, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 38 (by decide)))

theorem fz2_141_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨39, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 39 (by decide)))

theorem fz2_141_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨40, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 40 (by decide)))

theorem fz2_141_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨41, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 41 (by decide)))

theorem fz2_141_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨42, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 42 (by decide)))

theorem fz2_141_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨43, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 43 (by decide)))

theorem fz2_141_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨44, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 44 (by decide)))

theorem fz2_141_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨45, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 45 (by decide)))

theorem fz2_141_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨46, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 46 (by decide)))

theorem fz2_141_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨47, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 47 (by decide)))

theorem fz2_141_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨48, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 48 (by decide)))

theorem fz2_141_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨49, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 49 (by decide)))

theorem fz2_141_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨50, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 50 (by decide)))

theorem fz2_141_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨51, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 51 (by decide)))

theorem fz2_141_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨52, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 52 (by decide)))

theorem fz2_141_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨55, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 55 (by decide)))

theorem fz2_141_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨56, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 56 (by decide)))

theorem fz2_141_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨57, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 57 (by decide)))

theorem fz2_141_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨58, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 58 (by decide)))

theorem fz2_141_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨59, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 59 (by decide)))

theorem fz2_141_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨60, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 60 (by decide)))

theorem fz2_141_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨61, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 61 (by decide)))

theorem fz2_141_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨62, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 62 (by decide)))

theorem fz2_141_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨63, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 63 (by decide)))

theorem fz2_141_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨64, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 64 (by decide)))

theorem fz2_141_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨65, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 65 (by decide)))

theorem fz2_141_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨66, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 66 (by decide)))

theorem fz2_141_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨67, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 67 (by decide)))

theorem fz2_141_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨68, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 68 (by decide)))

theorem fz2_141_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨69, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 69 (by decide)))

theorem fz2_141_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨70, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 70 (by decide)))

theorem fz2_141_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨71, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 71 (by decide)))

theorem fz2_141_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨72, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 72 (by decide)))

theorem fz2_141_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨73, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 73 (by decide)))

theorem fz2_141_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨74, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 74 (by decide)))

theorem fz2_141_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨75, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 75 (by decide)))

theorem fz2_141_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨76, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 76 (by decide)))

theorem fz2_141_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨77, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 77 (by decide)))

theorem fz2_141_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨78, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 78 (by decide)))

theorem fz2_141_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨79, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 79 (by decide)))

theorem fz2_141_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨90, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 90 (by decide)))

theorem fz2_141_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨91, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 91 (by decide)))

theorem fz2_141_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨92, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 92 (by decide)))

theorem fz2_141_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨93, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 93 (by decide)))

theorem fz2_141_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨94, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 94 (by decide)))

theorem fz2_141_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨95, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 95 (by decide)))

theorem fz2_141_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨96, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 96 (by decide)))

theorem fz2_141_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨97, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 97 (by decide)))

theorem fz2_141_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨98, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 98 (by decide)))

theorem fz2_141_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨99, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 99 (by decide)))

theorem fz2_141_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨100, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 100 (by decide)))

theorem fz2_141_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨101, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 101 (by decide)))

theorem fz2_141_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨102, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 102 (by decide)))

theorem fz2_141_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨103, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 103 (by decide)))

theorem fz2_141_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨104, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 104 (by decide)))

theorem fz2_141_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨105, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 105 (by decide)))

theorem fz2_141_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨106, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 106 (by decide)))

theorem fz2_141_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨107, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 107 (by decide)))

theorem fz2_141_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨108, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 108 (by decide)))

theorem fz2_141_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨109, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 109 (by decide)))

theorem fz2_141_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨110, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 110 (by decide)))

theorem fz2_141_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨111, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 111 (by decide)))

theorem fz2_141_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨112, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 112 (by decide)))

theorem fz2_141_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨113, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 113 (by decide)))

theorem fz2_141_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨114, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 114 (by decide)))

theorem fz2_141_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨116, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 116 (by decide)))

theorem fz2_141_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨117, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 117 (by decide)))

theorem fz2_141_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨118, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 118 (by decide)))

theorem fz2_141_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨119, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 119 (by decide)))

theorem fz2_141_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨120, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 120 (by decide)))

theorem fz2_141_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨121, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 121 (by decide)))

theorem fz2_141_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨122, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 122 (by decide)))

theorem fz2_141_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨123, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 123 (by decide)))

theorem fz2_141_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨124, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 124 (by decide)))

theorem fz2_141_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨125, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 125 (by decide)))

theorem fz2_141_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨126, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 126 (by decide)))

theorem fz2_141_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨127, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 127 (by decide)))

theorem fz2_141_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨128, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 128 (by decide)))

theorem fz2_141_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨129, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 129 (by decide)))

theorem fz2_141_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨130, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 130 (by decide)))

theorem fz2_141_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨131, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 131 (by decide)))

theorem fz2_141_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨132, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 132 (by decide)))

theorem fz2_141_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨133, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 133 (by decide)))

theorem fz2_141_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨134, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 134 (by decide)))

theorem fz2_141_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨135, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 135 (by decide)))

theorem fz2_141_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨136, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 136 (by decide)))

theorem fz2_141_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨137, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 137 (by decide)))

theorem fz2_141_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨138, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 138 (by decide)))

theorem fz2_141_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨139, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 139 (by decide)))

theorem fz2_141_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨140, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 140 (by decide)))

theorem fz2_141_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨142, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 142 (by decide)))

theorem fz2_141_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨143, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 143 (by decide)))

theorem fz2_141_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨144, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 144 (by decide)))

theorem fz2_141_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨145, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 145 (by decide)))

theorem fz2_141_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK141)) = 0 :=
  Q2.repsFixedCard2 rK141 ⟨146, by decide⟩ Q2.R141_2 Q2.hpxR141_2 Q2.hcardq141_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_141) 146 (by decide)))

theorem fixz1_142 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK142) (retConj 1 (R142 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_142_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨1, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 1 (by decide)))

theorem fz1_142_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨2, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 2 (by decide)))

theorem fz1_142_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨3, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 3 (by decide)))

theorem fz1_142_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨4, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 4 (by decide)))

theorem fz1_142_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨5, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 5 (by decide)))

theorem fz1_142_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨6, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 6 (by decide)))

theorem fz1_142_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨7, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 7 (by decide)))

theorem fz1_142_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨8, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 8 (by decide)))

theorem fz1_142_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨9, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 9 (by decide)))

theorem fz1_142_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨13, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 13 (by decide)))

theorem fz1_142_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨14, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 14 (by decide)))

theorem fz1_142_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨15, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 15 (by decide)))

theorem fz1_142_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨16, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 16 (by decide)))

theorem fz1_142_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨17, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 17 (by decide)))

theorem fz1_142_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨18, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 18 (by decide)))

theorem fz1_142_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨19, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 19 (by decide)))

theorem fz1_142_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨20, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 20 (by decide)))

theorem fz1_142_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨21, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 21 (by decide)))

theorem fz1_142_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨22, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 22 (by decide)))

theorem fz1_142_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨23, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 23 (by decide)))

theorem fz1_142_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨24, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 24 (by decide)))

theorem fz1_142_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨25, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 25 (by decide)))

theorem fz1_142_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨26, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 26 (by decide)))

theorem fz1_142_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨27, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 27 (by decide)))

theorem fz1_142_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨33, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 33 (by decide)))

theorem fz1_142_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨34, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 34 (by decide)))

theorem fz1_142_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨35, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 35 (by decide)))

theorem fz1_142_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨36, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 36 (by decide)))

theorem fz1_142_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨37, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 37 (by decide)))

theorem fz1_142_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨38, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 38 (by decide)))

theorem fz1_142_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨39, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 39 (by decide)))

theorem fz1_142_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨40, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 40 (by decide)))

theorem fz1_142_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨41, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 41 (by decide)))

theorem fz1_142_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨42, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 42 (by decide)))

theorem fz1_142_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨43, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 43 (by decide)))

theorem fz1_142_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨44, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 44 (by decide)))

theorem fz1_142_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨45, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 45 (by decide)))

theorem fz1_142_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨46, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 46 (by decide)))

theorem fz1_142_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨47, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 47 (by decide)))

theorem fz1_142_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨48, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 48 (by decide)))

theorem fz1_142_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨49, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 49 (by decide)))

theorem fz1_142_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨50, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 50 (by decide)))

theorem fz1_142_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨51, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 51 (by decide)))

theorem fz1_142_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨52, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 52 (by decide)))

theorem fz1_142_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨55, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 55 (by decide)))

theorem fz1_142_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨56, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 56 (by decide)))

theorem fz1_142_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨57, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 57 (by decide)))

theorem fz1_142_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨58, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 58 (by decide)))

theorem fz1_142_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨59, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 59 (by decide)))

theorem fz1_142_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨60, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 60 (by decide)))

theorem fz1_142_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨61, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 61 (by decide)))

theorem fz1_142_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨62, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 62 (by decide)))

theorem fz1_142_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨63, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 63 (by decide)))

theorem fz1_142_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨64, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 64 (by decide)))

theorem fz1_142_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨65, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 65 (by decide)))

theorem fz1_142_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨66, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 66 (by decide)))

theorem fz1_142_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨67, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 67 (by decide)))

theorem fz1_142_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨68, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 68 (by decide)))

theorem fz1_142_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨69, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 69 (by decide)))

theorem fz1_142_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨70, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 70 (by decide)))

theorem fz1_142_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨71, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 71 (by decide)))

theorem fz1_142_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨72, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 72 (by decide)))

theorem fz1_142_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨73, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 73 (by decide)))

theorem fz1_142_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨74, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 74 (by decide)))

theorem fz1_142_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨75, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 75 (by decide)))

theorem fz1_142_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨76, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 76 (by decide)))

theorem fz1_142_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨77, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 77 (by decide)))

theorem fz1_142_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨78, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 78 (by decide)))

theorem fz1_142_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨79, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 79 (by decide)))

theorem fz1_142_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨80, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 80 (by decide)))

theorem fz1_142_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨81, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 81 (by decide)))

theorem fz1_142_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨82, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 82 (by decide)))

theorem fz1_142_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨83, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 83 (by decide)))

theorem fz1_142_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨84, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 84 (by decide)))

theorem fz1_142_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨85, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 85 (by decide)))

theorem fz1_142_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨86, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 86 (by decide)))

theorem fz1_142_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨87, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 87 (by decide)))

theorem fz1_142_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨88, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 88 (by decide)))

theorem fz1_142_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨89, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 89 (by decide)))

theorem fz1_142_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨95, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 95 (by decide)))

theorem fz1_142_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨96, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 96 (by decide)))

theorem fz1_142_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨97, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 97 (by decide)))

theorem fz1_142_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨98, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 98 (by decide)))

theorem fz1_142_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨99, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 99 (by decide)))

theorem fz1_142_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨100, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 100 (by decide)))

theorem fz1_142_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨101, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 101 (by decide)))

theorem fz1_142_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨102, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 102 (by decide)))

theorem fz1_142_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨103, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 103 (by decide)))

theorem fz1_142_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨104, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 104 (by decide)))

theorem fz1_142_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨105, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 105 (by decide)))

theorem fz1_142_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨106, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 106 (by decide)))

theorem fz1_142_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨107, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 107 (by decide)))

theorem fz1_142_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨108, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 108 (by decide)))

theorem fz1_142_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨109, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 109 (by decide)))

theorem fz1_142_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨110, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 110 (by decide)))

theorem fz1_142_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨111, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 111 (by decide)))

theorem fz1_142_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨112, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 112 (by decide)))

theorem fz1_142_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨113, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 113 (by decide)))

theorem fz1_142_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨114, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 114 (by decide)))

theorem fz1_142_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨116, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 116 (by decide)))

theorem fz1_142_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨117, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 117 (by decide)))

theorem fz1_142_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨118, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 118 (by decide)))

theorem fz1_142_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨119, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 119 (by decide)))

theorem fz1_142_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨120, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 120 (by decide)))

theorem fz1_142_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨121, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 121 (by decide)))

theorem fz1_142_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨122, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 122 (by decide)))

theorem fz1_142_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨123, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 123 (by decide)))

theorem fz1_142_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨124, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 124 (by decide)))

theorem fz1_142_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨125, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 125 (by decide)))

theorem fz1_142_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨126, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 126 (by decide)))

theorem fz1_142_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨127, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 127 (by decide)))

theorem fz1_142_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨128, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 128 (by decide)))

theorem fz1_142_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨129, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 129 (by decide)))

theorem fz1_142_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨130, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 130 (by decide)))

theorem fz1_142_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨131, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 131 (by decide)))

theorem fz1_142_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨132, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 132 (by decide)))

theorem fz1_142_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨133, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 133 (by decide)))

theorem fz1_142_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨134, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 134 (by decide)))

theorem fz1_142_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨135, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 135 (by decide)))

theorem fz1_142_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨136, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 136 (by decide)))

theorem fz1_142_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨137, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 137 (by decide)))

theorem fz1_142_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨138, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 138 (by decide)))

theorem fz1_142_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨139, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 139 (by decide)))

theorem fz1_142_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨140, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 140 (by decide)))

theorem fz1_142_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨141, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 141 (by decide)))

theorem fz1_142_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨143, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 143 (by decide)))

theorem fz1_142_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨144, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 144 (by decide)))

theorem fz1_142_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨145, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 145 (by decide)))

theorem fz1_142_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK142)) = 0 :=
  repsFixedCard rK142 ⟨146, by decide⟩ R142 hpxR142 hcardq142
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_142) 146 (by decide)))

theorem fixz2_142 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK142) (retConj 2 (Q2.R142_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_142_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨1, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 1 (by decide)))

theorem fz2_142_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨2, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 2 (by decide)))

theorem fz2_142_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨3, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 3 (by decide)))

theorem fz2_142_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨4, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 4 (by decide)))

theorem fz2_142_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨5, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 5 (by decide)))

theorem fz2_142_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨6, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 6 (by decide)))

theorem fz2_142_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨7, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 7 (by decide)))

theorem fz2_142_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨8, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 8 (by decide)))

theorem fz2_142_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨9, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 9 (by decide)))

theorem fz2_142_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨13, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 13 (by decide)))

theorem fz2_142_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨14, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 14 (by decide)))

theorem fz2_142_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨15, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 15 (by decide)))

theorem fz2_142_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨16, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 16 (by decide)))

theorem fz2_142_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨17, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 17 (by decide)))

theorem fz2_142_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨18, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 18 (by decide)))

theorem fz2_142_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨19, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 19 (by decide)))

theorem fz2_142_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨20, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 20 (by decide)))

theorem fz2_142_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨21, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 21 (by decide)))

theorem fz2_142_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨22, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 22 (by decide)))

theorem fz2_142_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨23, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 23 (by decide)))

theorem fz2_142_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨24, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 24 (by decide)))

theorem fz2_142_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨25, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 25 (by decide)))

theorem fz2_142_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨26, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 26 (by decide)))

theorem fz2_142_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨27, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 27 (by decide)))

theorem fz2_142_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨33, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 33 (by decide)))

theorem fz2_142_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨34, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 34 (by decide)))

theorem fz2_142_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨35, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 35 (by decide)))

theorem fz2_142_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨36, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 36 (by decide)))

theorem fz2_142_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨37, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 37 (by decide)))

theorem fz2_142_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨38, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 38 (by decide)))

theorem fz2_142_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨39, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 39 (by decide)))

theorem fz2_142_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨40, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 40 (by decide)))

theorem fz2_142_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨41, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 41 (by decide)))

theorem fz2_142_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨42, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 42 (by decide)))

theorem fz2_142_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨43, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 43 (by decide)))

theorem fz2_142_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨44, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 44 (by decide)))

theorem fz2_142_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨45, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 45 (by decide)))

theorem fz2_142_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨46, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 46 (by decide)))

theorem fz2_142_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨47, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 47 (by decide)))

theorem fz2_142_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨48, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 48 (by decide)))

theorem fz2_142_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨49, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 49 (by decide)))

theorem fz2_142_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨50, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 50 (by decide)))

theorem fz2_142_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨51, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 51 (by decide)))

theorem fz2_142_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨52, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 52 (by decide)))

theorem fz2_142_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨55, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 55 (by decide)))

theorem fz2_142_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨56, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 56 (by decide)))

theorem fz2_142_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨57, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 57 (by decide)))

theorem fz2_142_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨58, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 58 (by decide)))

theorem fz2_142_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨59, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 59 (by decide)))

theorem fz2_142_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨60, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 60 (by decide)))

theorem fz2_142_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨61, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 61 (by decide)))

theorem fz2_142_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨62, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 62 (by decide)))

theorem fz2_142_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨63, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 63 (by decide)))

theorem fz2_142_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨64, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 64 (by decide)))

theorem fz2_142_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨65, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 65 (by decide)))

theorem fz2_142_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨66, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 66 (by decide)))

theorem fz2_142_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨67, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 67 (by decide)))

theorem fz2_142_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨68, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 68 (by decide)))

theorem fz2_142_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨69, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 69 (by decide)))

theorem fz2_142_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨70, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 70 (by decide)))

theorem fz2_142_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨71, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 71 (by decide)))

theorem fz2_142_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨72, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 72 (by decide)))

theorem fz2_142_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨73, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 73 (by decide)))

theorem fz2_142_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨74, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 74 (by decide)))

theorem fz2_142_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨75, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 75 (by decide)))

theorem fz2_142_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨76, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 76 (by decide)))

theorem fz2_142_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨77, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 77 (by decide)))

theorem fz2_142_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨78, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 78 (by decide)))

theorem fz2_142_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨79, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 79 (by decide)))

theorem fz2_142_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨80, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 80 (by decide)))

theorem fz2_142_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨81, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 81 (by decide)))

theorem fz2_142_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨82, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 82 (by decide)))

theorem fz2_142_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨83, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 83 (by decide)))

theorem fz2_142_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨84, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 84 (by decide)))

theorem fz2_142_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨85, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 85 (by decide)))

theorem fz2_142_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨86, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 86 (by decide)))

theorem fz2_142_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨87, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 87 (by decide)))

theorem fz2_142_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨88, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 88 (by decide)))

theorem fz2_142_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨89, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 89 (by decide)))

theorem fz2_142_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨95, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 95 (by decide)))

theorem fz2_142_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨96, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 96 (by decide)))

theorem fz2_142_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨97, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 97 (by decide)))

theorem fz2_142_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨98, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 98 (by decide)))

theorem fz2_142_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨99, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 99 (by decide)))

theorem fz2_142_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨100, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 100 (by decide)))

theorem fz2_142_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨101, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 101 (by decide)))

theorem fz2_142_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨102, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 102 (by decide)))

theorem fz2_142_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨103, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 103 (by decide)))

theorem fz2_142_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨104, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 104 (by decide)))

theorem fz2_142_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨105, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 105 (by decide)))

theorem fz2_142_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨106, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 106 (by decide)))

theorem fz2_142_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨107, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 107 (by decide)))

theorem fz2_142_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨108, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 108 (by decide)))

theorem fz2_142_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨109, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 109 (by decide)))

theorem fz2_142_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨110, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 110 (by decide)))

theorem fz2_142_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨111, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 111 (by decide)))

theorem fz2_142_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨112, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 112 (by decide)))

theorem fz2_142_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨113, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 113 (by decide)))

theorem fz2_142_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨114, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 114 (by decide)))

theorem fz2_142_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨116, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 116 (by decide)))

theorem fz2_142_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨117, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 117 (by decide)))

theorem fz2_142_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨118, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 118 (by decide)))

theorem fz2_142_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨119, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 119 (by decide)))

theorem fz2_142_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨120, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 120 (by decide)))

theorem fz2_142_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨121, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 121 (by decide)))

theorem fz2_142_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨122, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 122 (by decide)))

theorem fz2_142_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨123, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 123 (by decide)))

theorem fz2_142_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨124, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 124 (by decide)))

theorem fz2_142_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨125, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 125 (by decide)))

theorem fz2_142_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨126, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 126 (by decide)))

theorem fz2_142_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨127, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 127 (by decide)))

theorem fz2_142_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨128, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 128 (by decide)))

theorem fz2_142_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨129, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 129 (by decide)))

theorem fz2_142_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨130, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 130 (by decide)))

theorem fz2_142_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨131, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 131 (by decide)))

theorem fz2_142_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨132, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 132 (by decide)))

theorem fz2_142_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨133, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 133 (by decide)))

theorem fz2_142_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨134, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 134 (by decide)))

theorem fz2_142_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨135, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 135 (by decide)))

theorem fz2_142_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨136, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 136 (by decide)))

theorem fz2_142_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨137, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 137 (by decide)))

theorem fz2_142_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨138, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 138 (by decide)))

theorem fz2_142_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨139, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 139 (by decide)))

theorem fz2_142_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨140, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 140 (by decide)))

theorem fz2_142_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨141, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 141 (by decide)))

theorem fz2_142_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨143, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 143 (by decide)))

theorem fz2_142_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨144, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 144 (by decide)))

theorem fz2_142_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨145, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 145 (by decide)))

theorem fz2_142_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK142)) = 0 :=
  Q2.repsFixedCard2 rK142 ⟨146, by decide⟩ Q2.R142_2 Q2.hpxR142_2 Q2.hcardq142_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_142) 146 (by decide)))

theorem fixz1_143 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK143) (retConj 1 (R143 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_143_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨1, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 1 (by decide)))

theorem fz1_143_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨2, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 2 (by decide)))

theorem fz1_143_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨3, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 3 (by decide)))

theorem fz1_143_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨4, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 4 (by decide)))

theorem fz1_143_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨5, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 5 (by decide)))

theorem fz1_143_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨6, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 6 (by decide)))

theorem fz1_143_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨7, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 7 (by decide)))

theorem fz1_143_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨8, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 8 (by decide)))

theorem fz1_143_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨9, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 9 (by decide)))

theorem fz1_143_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨13, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 13 (by decide)))

theorem fz1_143_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨14, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 14 (by decide)))

theorem fz1_143_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨15, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 15 (by decide)))

theorem fz1_143_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨16, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 16 (by decide)))

theorem fz1_143_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨17, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 17 (by decide)))

theorem fz1_143_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨18, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 18 (by decide)))

theorem fz1_143_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨19, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 19 (by decide)))

theorem fz1_143_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨20, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 20 (by decide)))

theorem fz1_143_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨21, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 21 (by decide)))

theorem fz1_143_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨22, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 22 (by decide)))

theorem fz1_143_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨23, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 23 (by decide)))

theorem fz1_143_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨24, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 24 (by decide)))

theorem fz1_143_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨25, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 25 (by decide)))

theorem fz1_143_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨26, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 26 (by decide)))

theorem fz1_143_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨27, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 27 (by decide)))

theorem fz1_143_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨28, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 28 (by decide)))

theorem fz1_143_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨29, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 29 (by decide)))

theorem fz1_143_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨30, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 30 (by decide)))

theorem fz1_143_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨31, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 31 (by decide)))

theorem fz1_143_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨32, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 32 (by decide)))

theorem fz1_143_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨38, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 38 (by decide)))

theorem fz1_143_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨39, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 39 (by decide)))

theorem fz1_143_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨40, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 40 (by decide)))

theorem fz1_143_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨41, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 41 (by decide)))

theorem fz1_143_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨42, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 42 (by decide)))

theorem fz1_143_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨43, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 43 (by decide)))

theorem fz1_143_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨44, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 44 (by decide)))

theorem fz1_143_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨45, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 45 (by decide)))

theorem fz1_143_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨46, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 46 (by decide)))

theorem fz1_143_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨47, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 47 (by decide)))

theorem fz1_143_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨48, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 48 (by decide)))

theorem fz1_143_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨49, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 49 (by decide)))

theorem fz1_143_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨50, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 50 (by decide)))

theorem fz1_143_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨51, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 51 (by decide)))

theorem fz1_143_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨52, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 52 (by decide)))

theorem fz1_143_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨55, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 55 (by decide)))

theorem fz1_143_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨56, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 56 (by decide)))

theorem fz1_143_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨57, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 57 (by decide)))

theorem fz1_143_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨58, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 58 (by decide)))

theorem fz1_143_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨59, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 59 (by decide)))

theorem fz1_143_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨60, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 60 (by decide)))

theorem fz1_143_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨61, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 61 (by decide)))

theorem fz1_143_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨62, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 62 (by decide)))

theorem fz1_143_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨63, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 63 (by decide)))

theorem fz1_143_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨64, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 64 (by decide)))

theorem fz1_143_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨65, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 65 (by decide)))

theorem fz1_143_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨66, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 66 (by decide)))

theorem fz1_143_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨67, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 67 (by decide)))

theorem fz1_143_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨68, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 68 (by decide)))

theorem fz1_143_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨69, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 69 (by decide)))

theorem fz1_143_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨70, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 70 (by decide)))

theorem fz1_143_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨71, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 71 (by decide)))

theorem fz1_143_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨72, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 72 (by decide)))

theorem fz1_143_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨73, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 73 (by decide)))

theorem fz1_143_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨74, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 74 (by decide)))

theorem fz1_143_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨75, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 75 (by decide)))

theorem fz1_143_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨76, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 76 (by decide)))

theorem fz1_143_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨77, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 77 (by decide)))

theorem fz1_143_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨78, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 78 (by decide)))

theorem fz1_143_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨79, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 79 (by decide)))

theorem fz1_143_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨80, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 80 (by decide)))

theorem fz1_143_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨81, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 81 (by decide)))

theorem fz1_143_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨82, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 82 (by decide)))

theorem fz1_143_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨83, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 83 (by decide)))

theorem fz1_143_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨84, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 84 (by decide)))

theorem fz1_143_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨85, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 85 (by decide)))

theorem fz1_143_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨86, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 86 (by decide)))

theorem fz1_143_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨87, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 87 (by decide)))

theorem fz1_143_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨88, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 88 (by decide)))

theorem fz1_143_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨89, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 89 (by decide)))

theorem fz1_143_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨90, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 90 (by decide)))

theorem fz1_143_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨91, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 91 (by decide)))

theorem fz1_143_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨92, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 92 (by decide)))

theorem fz1_143_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨93, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 93 (by decide)))

theorem fz1_143_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨94, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 94 (by decide)))

theorem fz1_143_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨100, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 100 (by decide)))

theorem fz1_143_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨101, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 101 (by decide)))

theorem fz1_143_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨102, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 102 (by decide)))

theorem fz1_143_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨103, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 103 (by decide)))

theorem fz1_143_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨104, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 104 (by decide)))

theorem fz1_143_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨105, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 105 (by decide)))

theorem fz1_143_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨106, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 106 (by decide)))

theorem fz1_143_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨107, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 107 (by decide)))

theorem fz1_143_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨108, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 108 (by decide)))

theorem fz1_143_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨109, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 109 (by decide)))

theorem fz1_143_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨110, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 110 (by decide)))

theorem fz1_143_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨111, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 111 (by decide)))

theorem fz1_143_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨112, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 112 (by decide)))

theorem fz1_143_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨113, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 113 (by decide)))

theorem fz1_143_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨114, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 114 (by decide)))

theorem fz1_143_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨116, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 116 (by decide)))

theorem fz1_143_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨117, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 117 (by decide)))

theorem fz1_143_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨118, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 118 (by decide)))

theorem fz1_143_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨119, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 119 (by decide)))

theorem fz1_143_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨120, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 120 (by decide)))

theorem fz1_143_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨121, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 121 (by decide)))

theorem fz1_143_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨122, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 122 (by decide)))

theorem fz1_143_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨123, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 123 (by decide)))

theorem fz1_143_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨124, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 124 (by decide)))

theorem fz1_143_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨125, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 125 (by decide)))

theorem fz1_143_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨126, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 126 (by decide)))

theorem fz1_143_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨127, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 127 (by decide)))

theorem fz1_143_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨128, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 128 (by decide)))

theorem fz1_143_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨129, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 129 (by decide)))

theorem fz1_143_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨130, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 130 (by decide)))

theorem fz1_143_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨131, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 131 (by decide)))

theorem fz1_143_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨132, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 132 (by decide)))

theorem fz1_143_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨133, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 133 (by decide)))

theorem fz1_143_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨134, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 134 (by decide)))

theorem fz1_143_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨135, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 135 (by decide)))

theorem fz1_143_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨136, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 136 (by decide)))

theorem fz1_143_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨137, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 137 (by decide)))

theorem fz1_143_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨138, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 138 (by decide)))

theorem fz1_143_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨139, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 139 (by decide)))

theorem fz1_143_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨140, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 140 (by decide)))

theorem fz1_143_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨141, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 141 (by decide)))

theorem fz1_143_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨142, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 142 (by decide)))

theorem fz1_143_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨144, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 144 (by decide)))

theorem fz1_143_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨145, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 145 (by decide)))

theorem fz1_143_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK143)) = 0 :=
  repsFixedCard rK143 ⟨146, by decide⟩ R143 hpxR143 hcardq143
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_143) 146 (by decide)))

theorem fixz2_143 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK143) (retConj 2 (Q2.R143_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_143_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨1, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 1 (by decide)))

theorem fz2_143_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨2, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 2 (by decide)))

theorem fz2_143_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨3, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 3 (by decide)))

theorem fz2_143_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨4, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 4 (by decide)))

theorem fz2_143_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨5, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 5 (by decide)))

theorem fz2_143_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨6, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 6 (by decide)))

theorem fz2_143_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨7, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 7 (by decide)))

theorem fz2_143_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨8, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 8 (by decide)))

theorem fz2_143_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨9, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 9 (by decide)))

theorem fz2_143_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨13, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 13 (by decide)))

theorem fz2_143_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨14, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 14 (by decide)))

theorem fz2_143_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨15, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 15 (by decide)))

theorem fz2_143_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨16, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 16 (by decide)))

theorem fz2_143_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨17, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 17 (by decide)))

theorem fz2_143_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨18, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 18 (by decide)))

theorem fz2_143_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨19, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 19 (by decide)))

theorem fz2_143_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨20, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 20 (by decide)))

theorem fz2_143_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨21, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 21 (by decide)))

theorem fz2_143_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨22, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 22 (by decide)))

theorem fz2_143_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨23, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 23 (by decide)))

theorem fz2_143_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨24, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 24 (by decide)))

theorem fz2_143_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨25, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 25 (by decide)))

theorem fz2_143_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨26, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 26 (by decide)))

theorem fz2_143_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨27, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 27 (by decide)))

theorem fz2_143_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨28, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 28 (by decide)))

theorem fz2_143_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨29, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 29 (by decide)))

theorem fz2_143_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨30, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 30 (by decide)))

theorem fz2_143_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨31, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 31 (by decide)))

theorem fz2_143_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨32, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 32 (by decide)))

theorem fz2_143_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨38, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 38 (by decide)))

theorem fz2_143_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨39, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 39 (by decide)))

theorem fz2_143_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨40, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 40 (by decide)))

theorem fz2_143_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨41, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 41 (by decide)))

theorem fz2_143_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨42, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 42 (by decide)))

theorem fz2_143_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨43, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 43 (by decide)))

theorem fz2_143_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨44, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 44 (by decide)))

theorem fz2_143_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨45, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 45 (by decide)))

theorem fz2_143_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨46, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 46 (by decide)))

theorem fz2_143_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨47, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 47 (by decide)))

theorem fz2_143_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨48, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 48 (by decide)))

theorem fz2_143_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨49, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 49 (by decide)))

theorem fz2_143_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨50, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 50 (by decide)))

theorem fz2_143_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨51, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 51 (by decide)))

theorem fz2_143_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨52, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 52 (by decide)))

theorem fz2_143_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨55, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 55 (by decide)))

theorem fz2_143_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨56, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 56 (by decide)))

theorem fz2_143_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨57, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 57 (by decide)))

theorem fz2_143_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨58, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 58 (by decide)))

theorem fz2_143_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨59, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 59 (by decide)))

theorem fz2_143_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨60, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 60 (by decide)))

theorem fz2_143_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨61, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 61 (by decide)))

theorem fz2_143_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨62, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 62 (by decide)))

theorem fz2_143_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨63, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 63 (by decide)))

theorem fz2_143_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨64, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 64 (by decide)))

theorem fz2_143_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨65, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 65 (by decide)))

theorem fz2_143_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨66, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 66 (by decide)))

theorem fz2_143_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨67, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 67 (by decide)))

theorem fz2_143_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨68, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 68 (by decide)))

theorem fz2_143_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨69, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 69 (by decide)))

theorem fz2_143_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨70, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 70 (by decide)))

theorem fz2_143_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨71, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 71 (by decide)))

theorem fz2_143_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨72, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 72 (by decide)))

theorem fz2_143_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨73, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 73 (by decide)))

theorem fz2_143_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨74, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 74 (by decide)))

theorem fz2_143_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨75, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 75 (by decide)))

theorem fz2_143_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨76, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 76 (by decide)))

theorem fz2_143_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨77, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 77 (by decide)))

theorem fz2_143_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨78, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 78 (by decide)))

theorem fz2_143_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨79, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 79 (by decide)))

theorem fz2_143_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨80, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 80 (by decide)))

theorem fz2_143_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨81, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 81 (by decide)))

theorem fz2_143_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨82, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 82 (by decide)))

theorem fz2_143_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨83, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 83 (by decide)))

theorem fz2_143_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨84, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 84 (by decide)))

theorem fz2_143_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨85, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 85 (by decide)))

theorem fz2_143_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨86, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 86 (by decide)))

theorem fz2_143_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨87, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 87 (by decide)))

theorem fz2_143_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨88, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 88 (by decide)))

theorem fz2_143_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨89, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 89 (by decide)))

theorem fz2_143_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨90, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 90 (by decide)))

theorem fz2_143_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨91, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 91 (by decide)))

theorem fz2_143_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨92, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 92 (by decide)))

theorem fz2_143_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨93, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 93 (by decide)))

theorem fz2_143_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨94, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 94 (by decide)))

theorem fz2_143_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨100, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 100 (by decide)))

theorem fz2_143_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨101, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 101 (by decide)))

theorem fz2_143_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨102, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 102 (by decide)))

theorem fz2_143_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨103, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 103 (by decide)))

theorem fz2_143_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨104, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 104 (by decide)))

theorem fz2_143_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨105, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 105 (by decide)))

theorem fz2_143_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨106, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 106 (by decide)))

theorem fz2_143_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨107, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 107 (by decide)))

theorem fz2_143_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨108, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 108 (by decide)))

theorem fz2_143_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨109, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 109 (by decide)))

theorem fz2_143_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨110, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 110 (by decide)))

theorem fz2_143_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨111, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 111 (by decide)))

theorem fz2_143_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨112, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 112 (by decide)))

theorem fz2_143_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨113, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 113 (by decide)))

theorem fz2_143_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨114, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 114 (by decide)))

theorem fz2_143_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨116, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 116 (by decide)))

theorem fz2_143_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨117, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 117 (by decide)))

theorem fz2_143_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨118, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 118 (by decide)))

theorem fz2_143_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨119, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 119 (by decide)))

theorem fz2_143_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨120, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 120 (by decide)))

theorem fz2_143_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨121, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 121 (by decide)))

theorem fz2_143_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨122, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 122 (by decide)))

theorem fz2_143_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨123, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 123 (by decide)))

theorem fz2_143_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨124, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 124 (by decide)))

theorem fz2_143_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨125, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 125 (by decide)))

theorem fz2_143_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨126, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 126 (by decide)))

theorem fz2_143_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨127, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 127 (by decide)))

theorem fz2_143_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨128, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 128 (by decide)))

theorem fz2_143_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨129, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 129 (by decide)))

theorem fz2_143_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨130, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 130 (by decide)))

theorem fz2_143_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨131, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 131 (by decide)))

theorem fz2_143_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨132, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 132 (by decide)))

theorem fz2_143_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨133, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 133 (by decide)))

theorem fz2_143_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨134, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 134 (by decide)))

theorem fz2_143_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨135, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 135 (by decide)))

theorem fz2_143_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨136, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 136 (by decide)))

theorem fz2_143_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨137, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 137 (by decide)))

theorem fz2_143_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨138, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 138 (by decide)))

theorem fz2_143_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨139, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 139 (by decide)))

theorem fz2_143_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨140, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 140 (by decide)))

theorem fz2_143_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨141, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 141 (by decide)))

theorem fz2_143_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨142, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 142 (by decide)))

theorem fz2_143_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨144, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 144 (by decide)))

theorem fz2_143_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨145, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 145 (by decide)))

theorem fz2_143_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK143)) = 0 :=
  Q2.repsFixedCard2 rK143 ⟨146, by decide⟩ Q2.R143_2 Q2.hpxR143_2 Q2.hcardq143_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_143) 146 (by decide)))

theorem fixz1_144 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK144) (retConj 1 (R144 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_144_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨1, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 1 (by decide)))

theorem fz1_144_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨2, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 2 (by decide)))

theorem fz1_144_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨3, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 3 (by decide)))

theorem fz1_144_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨4, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 4 (by decide)))

theorem fz1_144_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨5, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 5 (by decide)))

theorem fz1_144_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨6, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 6 (by decide)))

theorem fz1_144_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨7, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 7 (by decide)))

theorem fz1_144_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨8, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 8 (by decide)))

theorem fz1_144_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨9, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 9 (by decide)))

theorem fz1_144_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨13, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 13 (by decide)))

theorem fz1_144_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨14, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 14 (by decide)))

theorem fz1_144_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨15, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 15 (by decide)))

theorem fz1_144_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨16, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 16 (by decide)))

theorem fz1_144_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨17, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 17 (by decide)))

theorem fz1_144_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨18, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 18 (by decide)))

theorem fz1_144_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨19, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 19 (by decide)))

theorem fz1_144_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨20, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 20 (by decide)))

theorem fz1_144_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨21, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 21 (by decide)))

theorem fz1_144_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨22, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 22 (by decide)))

theorem fz1_144_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨23, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 23 (by decide)))

theorem fz1_144_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨24, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 24 (by decide)))

theorem fz1_144_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨25, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 25 (by decide)))

theorem fz1_144_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨26, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 26 (by decide)))

theorem fz1_144_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨27, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 27 (by decide)))

theorem fz1_144_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨28, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 28 (by decide)))

theorem fz1_144_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨29, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 29 (by decide)))

theorem fz1_144_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨30, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 30 (by decide)))

theorem fz1_144_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨31, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 31 (by decide)))

theorem fz1_144_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨32, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 32 (by decide)))

theorem fz1_144_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨33, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 33 (by decide)))

theorem fz1_144_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨34, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 34 (by decide)))

theorem fz1_144_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨35, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 35 (by decide)))

theorem fz1_144_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨36, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 36 (by decide)))

theorem fz1_144_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨37, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 37 (by decide)))

theorem fz1_144_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨43, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 43 (by decide)))

theorem fz1_144_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨44, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 44 (by decide)))

theorem fz1_144_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨45, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 45 (by decide)))

theorem fz1_144_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨46, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 46 (by decide)))

theorem fz1_144_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨47, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 47 (by decide)))

theorem fz1_144_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨48, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 48 (by decide)))

theorem fz1_144_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨49, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 49 (by decide)))

theorem fz1_144_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨50, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 50 (by decide)))

theorem fz1_144_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨51, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 51 (by decide)))

theorem fz1_144_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨52, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 52 (by decide)))

theorem fz1_144_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨55, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 55 (by decide)))

theorem fz1_144_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨56, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 56 (by decide)))

theorem fz1_144_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨57, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 57 (by decide)))

theorem fz1_144_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨58, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 58 (by decide)))

theorem fz1_144_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨59, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 59 (by decide)))

theorem fz1_144_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨60, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 60 (by decide)))

theorem fz1_144_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨61, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 61 (by decide)))

theorem fz1_144_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨62, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 62 (by decide)))

theorem fz1_144_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨63, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 63 (by decide)))

theorem fz1_144_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨64, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 64 (by decide)))

theorem fz1_144_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨65, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 65 (by decide)))

theorem fz1_144_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨66, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 66 (by decide)))

theorem fz1_144_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨67, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 67 (by decide)))

theorem fz1_144_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨68, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 68 (by decide)))

theorem fz1_144_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨69, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 69 (by decide)))

theorem fz1_144_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨70, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 70 (by decide)))

theorem fz1_144_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨71, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 71 (by decide)))

theorem fz1_144_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨72, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 72 (by decide)))

theorem fz1_144_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨73, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 73 (by decide)))

theorem fz1_144_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨74, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 74 (by decide)))

theorem fz1_144_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨75, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 75 (by decide)))

theorem fz1_144_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨76, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 76 (by decide)))

theorem fz1_144_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨77, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 77 (by decide)))

theorem fz1_144_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨78, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 78 (by decide)))

theorem fz1_144_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨79, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 79 (by decide)))

theorem fz1_144_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨80, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 80 (by decide)))

theorem fz1_144_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨81, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 81 (by decide)))

theorem fz1_144_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨82, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 82 (by decide)))

theorem fz1_144_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨83, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 83 (by decide)))

theorem fz1_144_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨84, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 84 (by decide)))

theorem fz1_144_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨85, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 85 (by decide)))

theorem fz1_144_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨86, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 86 (by decide)))

theorem fz1_144_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨87, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 87 (by decide)))

theorem fz1_144_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨88, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 88 (by decide)))

theorem fz1_144_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨89, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 89 (by decide)))

theorem fz1_144_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨90, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 90 (by decide)))

theorem fz1_144_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨91, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 91 (by decide)))

theorem fz1_144_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨92, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 92 (by decide)))

theorem fz1_144_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨93, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 93 (by decide)))

theorem fz1_144_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨94, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 94 (by decide)))

theorem fz1_144_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨95, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 95 (by decide)))

theorem fz1_144_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨96, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 96 (by decide)))

theorem fz1_144_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨97, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 97 (by decide)))

theorem fz1_144_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨98, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 98 (by decide)))

theorem fz1_144_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨99, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 99 (by decide)))

theorem fz1_144_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨105, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 105 (by decide)))

theorem fz1_144_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨106, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 106 (by decide)))

theorem fz1_144_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨107, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 107 (by decide)))

theorem fz1_144_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨108, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 108 (by decide)))

theorem fz1_144_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨109, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 109 (by decide)))

theorem fz1_144_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨110, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 110 (by decide)))

theorem fz1_144_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨111, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 111 (by decide)))

theorem fz1_144_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨112, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 112 (by decide)))

theorem fz1_144_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨113, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 113 (by decide)))

theorem fz1_144_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨114, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 114 (by decide)))

theorem fz1_144_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨116, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 116 (by decide)))

theorem fz1_144_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨117, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 117 (by decide)))

theorem fz1_144_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨118, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 118 (by decide)))

theorem fz1_144_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨119, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 119 (by decide)))

theorem fz1_144_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨120, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 120 (by decide)))

theorem fz1_144_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨121, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 121 (by decide)))

theorem fz1_144_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨122, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 122 (by decide)))

theorem fz1_144_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨123, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 123 (by decide)))

theorem fz1_144_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨124, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 124 (by decide)))

theorem fz1_144_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨125, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 125 (by decide)))

theorem fz1_144_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨126, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 126 (by decide)))

theorem fz1_144_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨127, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 127 (by decide)))

theorem fz1_144_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨128, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 128 (by decide)))

theorem fz1_144_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨129, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 129 (by decide)))

theorem fz1_144_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨130, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 130 (by decide)))

theorem fz1_144_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨131, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 131 (by decide)))

theorem fz1_144_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨132, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 132 (by decide)))

theorem fz1_144_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨133, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 133 (by decide)))

theorem fz1_144_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨134, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 134 (by decide)))

theorem fz1_144_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨135, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 135 (by decide)))

theorem fz1_144_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨136, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 136 (by decide)))

theorem fz1_144_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨137, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 137 (by decide)))

theorem fz1_144_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨138, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 138 (by decide)))

theorem fz1_144_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨139, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 139 (by decide)))

theorem fz1_144_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨140, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 140 (by decide)))

theorem fz1_144_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨141, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 141 (by decide)))

theorem fz1_144_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨142, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 142 (by decide)))

theorem fz1_144_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨143, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 143 (by decide)))

theorem fz1_144_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨145, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 145 (by decide)))

theorem fz1_144_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK144)) = 0 :=
  repsFixedCard rK144 ⟨146, by decide⟩ R144 hpxR144 hcardq144
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_144) 146 (by decide)))

theorem fixz2_144 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK144) (retConj 2 (Q2.R144_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_144_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨1, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 1 (by decide)))

theorem fz2_144_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨2, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 2 (by decide)))

theorem fz2_144_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨3, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 3 (by decide)))

theorem fz2_144_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨4, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 4 (by decide)))

theorem fz2_144_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨5, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 5 (by decide)))

theorem fz2_144_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨6, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 6 (by decide)))

theorem fz2_144_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨7, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 7 (by decide)))

theorem fz2_144_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨8, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 8 (by decide)))

theorem fz2_144_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨9, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 9 (by decide)))

theorem fz2_144_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨13, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 13 (by decide)))

theorem fz2_144_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨14, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 14 (by decide)))

theorem fz2_144_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨15, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 15 (by decide)))

theorem fz2_144_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨16, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 16 (by decide)))

theorem fz2_144_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨17, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 17 (by decide)))

theorem fz2_144_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨18, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 18 (by decide)))

theorem fz2_144_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨19, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 19 (by decide)))

theorem fz2_144_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨20, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 20 (by decide)))

theorem fz2_144_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨21, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 21 (by decide)))

theorem fz2_144_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨22, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 22 (by decide)))

theorem fz2_144_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨23, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 23 (by decide)))

theorem fz2_144_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨24, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 24 (by decide)))

theorem fz2_144_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨25, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 25 (by decide)))

theorem fz2_144_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨26, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 26 (by decide)))

theorem fz2_144_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨27, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 27 (by decide)))

theorem fz2_144_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨28, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 28 (by decide)))

theorem fz2_144_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨29, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 29 (by decide)))

theorem fz2_144_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨30, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 30 (by decide)))

theorem fz2_144_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨31, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 31 (by decide)))

theorem fz2_144_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨32, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 32 (by decide)))

theorem fz2_144_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨33, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 33 (by decide)))

theorem fz2_144_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨34, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 34 (by decide)))

theorem fz2_144_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨35, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 35 (by decide)))

theorem fz2_144_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨36, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 36 (by decide)))

theorem fz2_144_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨37, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 37 (by decide)))

theorem fz2_144_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨43, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 43 (by decide)))

theorem fz2_144_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨44, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 44 (by decide)))

theorem fz2_144_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨45, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 45 (by decide)))

theorem fz2_144_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨46, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 46 (by decide)))

theorem fz2_144_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨47, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 47 (by decide)))

theorem fz2_144_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨48, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 48 (by decide)))

theorem fz2_144_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨49, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 49 (by decide)))

theorem fz2_144_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨50, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 50 (by decide)))

theorem fz2_144_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨51, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 51 (by decide)))

theorem fz2_144_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨52, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 52 (by decide)))

theorem fz2_144_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨55, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 55 (by decide)))

theorem fz2_144_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨56, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 56 (by decide)))

theorem fz2_144_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨57, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 57 (by decide)))

theorem fz2_144_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨58, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 58 (by decide)))

theorem fz2_144_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨59, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 59 (by decide)))

theorem fz2_144_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨60, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 60 (by decide)))

theorem fz2_144_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨61, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 61 (by decide)))

theorem fz2_144_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨62, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 62 (by decide)))

theorem fz2_144_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨63, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 63 (by decide)))

theorem fz2_144_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨64, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 64 (by decide)))

theorem fz2_144_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨65, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 65 (by decide)))

theorem fz2_144_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨66, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 66 (by decide)))

theorem fz2_144_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨67, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 67 (by decide)))

theorem fz2_144_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨68, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 68 (by decide)))

theorem fz2_144_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨69, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 69 (by decide)))

theorem fz2_144_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨70, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 70 (by decide)))

theorem fz2_144_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨71, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 71 (by decide)))

theorem fz2_144_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨72, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 72 (by decide)))

theorem fz2_144_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨73, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 73 (by decide)))

theorem fz2_144_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨74, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 74 (by decide)))

theorem fz2_144_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨75, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 75 (by decide)))

theorem fz2_144_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨76, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 76 (by decide)))

theorem fz2_144_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨77, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 77 (by decide)))

theorem fz2_144_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨78, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 78 (by decide)))

theorem fz2_144_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨79, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 79 (by decide)))

theorem fz2_144_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨80, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 80 (by decide)))

theorem fz2_144_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨81, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 81 (by decide)))

theorem fz2_144_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨82, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 82 (by decide)))

theorem fz2_144_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨83, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 83 (by decide)))

theorem fz2_144_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨84, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 84 (by decide)))

theorem fz2_144_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨85, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 85 (by decide)))

theorem fz2_144_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨86, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 86 (by decide)))

theorem fz2_144_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨87, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 87 (by decide)))

theorem fz2_144_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨88, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 88 (by decide)))

theorem fz2_144_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨89, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 89 (by decide)))

theorem fz2_144_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨90, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 90 (by decide)))

theorem fz2_144_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨91, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 91 (by decide)))

theorem fz2_144_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨92, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 92 (by decide)))

theorem fz2_144_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨93, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 93 (by decide)))

theorem fz2_144_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨94, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 94 (by decide)))

theorem fz2_144_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨95, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 95 (by decide)))

theorem fz2_144_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨96, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 96 (by decide)))

theorem fz2_144_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨97, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 97 (by decide)))

theorem fz2_144_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨98, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 98 (by decide)))

theorem fz2_144_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨99, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 99 (by decide)))

theorem fz2_144_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨105, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 105 (by decide)))

theorem fz2_144_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨106, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 106 (by decide)))

theorem fz2_144_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨107, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 107 (by decide)))

theorem fz2_144_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨108, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 108 (by decide)))

theorem fz2_144_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨109, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 109 (by decide)))

theorem fz2_144_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨110, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 110 (by decide)))

theorem fz2_144_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨111, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 111 (by decide)))

theorem fz2_144_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨112, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 112 (by decide)))

theorem fz2_144_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨113, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 113 (by decide)))

theorem fz2_144_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨114, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 114 (by decide)))

theorem fz2_144_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨116, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 116 (by decide)))

theorem fz2_144_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨117, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 117 (by decide)))

theorem fz2_144_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨118, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 118 (by decide)))

theorem fz2_144_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨119, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 119 (by decide)))

theorem fz2_144_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨120, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 120 (by decide)))

theorem fz2_144_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨121, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 121 (by decide)))

theorem fz2_144_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨122, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 122 (by decide)))

theorem fz2_144_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨123, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 123 (by decide)))

theorem fz2_144_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨124, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 124 (by decide)))

theorem fz2_144_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨125, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 125 (by decide)))

theorem fz2_144_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨126, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 126 (by decide)))

theorem fz2_144_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨127, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 127 (by decide)))

theorem fz2_144_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨128, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 128 (by decide)))

theorem fz2_144_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨129, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 129 (by decide)))

theorem fz2_144_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨130, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 130 (by decide)))

theorem fz2_144_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨131, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 131 (by decide)))

theorem fz2_144_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨132, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 132 (by decide)))

theorem fz2_144_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨133, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 133 (by decide)))

theorem fz2_144_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨134, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 134 (by decide)))

theorem fz2_144_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨135, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 135 (by decide)))

theorem fz2_144_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨136, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 136 (by decide)))

theorem fz2_144_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨137, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 137 (by decide)))

theorem fz2_144_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨138, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 138 (by decide)))

theorem fz2_144_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨139, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 139 (by decide)))

theorem fz2_144_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨140, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 140 (by decide)))

theorem fz2_144_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨141, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 141 (by decide)))

theorem fz2_144_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨142, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 142 (by decide)))

theorem fz2_144_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨143, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 143 (by decide)))

theorem fz2_144_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨145, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 145 (by decide)))

theorem fz2_144_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK144)) = 0 :=
  Q2.repsFixedCard2 rK144 ⟨146, by decide⟩ Q2.R144_2 Q2.hpxR144_2 Q2.hcardq144_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_144) 146 (by decide)))

theorem fixz1_145 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 110, 111, 112, 113, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK145) (retConj 1 (R145 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_145_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨1, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 1 (by decide)))

theorem fz1_145_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨2, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 2 (by decide)))

theorem fz1_145_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨3, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 3 (by decide)))

theorem fz1_145_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨4, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 4 (by decide)))

theorem fz1_145_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨5, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 5 (by decide)))

theorem fz1_145_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨6, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 6 (by decide)))

theorem fz1_145_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨7, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 7 (by decide)))

theorem fz1_145_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨8, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 8 (by decide)))

theorem fz1_145_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨9, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 9 (by decide)))

theorem fz1_145_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨13, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 13 (by decide)))

theorem fz1_145_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨14, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 14 (by decide)))

theorem fz1_145_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨15, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 15 (by decide)))

theorem fz1_145_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨16, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 16 (by decide)))

theorem fz1_145_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨17, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 17 (by decide)))

theorem fz1_145_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨18, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 18 (by decide)))

theorem fz1_145_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨19, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 19 (by decide)))

theorem fz1_145_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨20, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 20 (by decide)))

theorem fz1_145_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨21, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 21 (by decide)))

theorem fz1_145_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨22, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 22 (by decide)))

theorem fz1_145_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨23, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 23 (by decide)))

theorem fz1_145_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨24, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 24 (by decide)))

theorem fz1_145_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨25, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 25 (by decide)))

theorem fz1_145_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨26, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 26 (by decide)))

theorem fz1_145_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨27, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 27 (by decide)))

theorem fz1_145_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨28, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 28 (by decide)))

theorem fz1_145_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨29, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 29 (by decide)))

theorem fz1_145_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨30, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 30 (by decide)))

theorem fz1_145_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨31, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 31 (by decide)))

theorem fz1_145_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨32, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 32 (by decide)))

theorem fz1_145_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨33, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 33 (by decide)))

theorem fz1_145_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨34, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 34 (by decide)))

theorem fz1_145_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨35, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 35 (by decide)))

theorem fz1_145_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨36, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 36 (by decide)))

theorem fz1_145_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨37, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 37 (by decide)))

theorem fz1_145_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨38, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 38 (by decide)))

theorem fz1_145_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨39, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 39 (by decide)))

theorem fz1_145_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨40, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 40 (by decide)))

theorem fz1_145_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨41, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 41 (by decide)))

theorem fz1_145_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨42, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 42 (by decide)))

theorem fz1_145_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨48, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 48 (by decide)))

theorem fz1_145_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨49, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 49 (by decide)))

theorem fz1_145_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨50, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 50 (by decide)))

theorem fz1_145_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨51, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 51 (by decide)))

theorem fz1_145_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨52, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 52 (by decide)))

theorem fz1_145_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨55, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 55 (by decide)))

theorem fz1_145_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨56, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 56 (by decide)))

theorem fz1_145_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨57, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 57 (by decide)))

theorem fz1_145_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨58, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 58 (by decide)))

theorem fz1_145_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨59, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 59 (by decide)))

theorem fz1_145_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨60, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 60 (by decide)))

theorem fz1_145_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨61, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 61 (by decide)))

theorem fz1_145_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨62, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 62 (by decide)))

theorem fz1_145_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨63, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 63 (by decide)))

theorem fz1_145_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨64, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 64 (by decide)))

theorem fz1_145_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨65, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 65 (by decide)))

theorem fz1_145_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨66, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 66 (by decide)))

theorem fz1_145_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨67, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 67 (by decide)))

theorem fz1_145_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨68, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 68 (by decide)))

theorem fz1_145_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨69, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 69 (by decide)))

theorem fz1_145_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨70, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 70 (by decide)))

theorem fz1_145_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨71, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 71 (by decide)))

theorem fz1_145_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨72, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 72 (by decide)))

theorem fz1_145_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨73, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 73 (by decide)))

theorem fz1_145_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨74, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 74 (by decide)))

theorem fz1_145_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨75, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 75 (by decide)))

theorem fz1_145_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨76, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 76 (by decide)))

theorem fz1_145_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨77, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 77 (by decide)))

theorem fz1_145_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨78, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 78 (by decide)))

theorem fz1_145_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨79, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 79 (by decide)))

theorem fz1_145_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨80, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 80 (by decide)))

theorem fz1_145_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨81, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 81 (by decide)))

theorem fz1_145_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨82, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 82 (by decide)))

theorem fz1_145_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨83, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 83 (by decide)))

theorem fz1_145_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨84, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 84 (by decide)))

theorem fz1_145_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨85, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 85 (by decide)))

theorem fz1_145_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨86, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 86 (by decide)))

theorem fz1_145_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨87, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 87 (by decide)))

theorem fz1_145_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨88, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 88 (by decide)))

theorem fz1_145_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨89, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 89 (by decide)))

theorem fz1_145_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨90, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 90 (by decide)))

theorem fz1_145_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨91, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 91 (by decide)))

theorem fz1_145_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨92, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 92 (by decide)))

theorem fz1_145_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨93, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 93 (by decide)))

theorem fz1_145_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨94, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 94 (by decide)))

theorem fz1_145_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨95, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 95 (by decide)))

theorem fz1_145_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨96, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 96 (by decide)))

theorem fz1_145_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨97, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 97 (by decide)))

theorem fz1_145_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨98, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 98 (by decide)))

theorem fz1_145_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨99, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 99 (by decide)))

theorem fz1_145_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨100, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 100 (by decide)))

theorem fz1_145_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨101, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 101 (by decide)))

theorem fz1_145_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨102, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 102 (by decide)))

theorem fz1_145_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨103, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 103 (by decide)))

theorem fz1_145_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨104, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 104 (by decide)))

theorem fz1_145_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨110, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 110 (by decide)))

theorem fz1_145_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨111, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 111 (by decide)))

theorem fz1_145_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨112, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 112 (by decide)))

theorem fz1_145_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨113, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 113 (by decide)))

theorem fz1_145_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨114, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 114 (by decide)))

theorem fz1_145_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨116, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 116 (by decide)))

theorem fz1_145_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨117, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 117 (by decide)))

theorem fz1_145_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨118, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 118 (by decide)))

theorem fz1_145_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨119, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 119 (by decide)))

theorem fz1_145_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨120, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 120 (by decide)))

theorem fz1_145_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨121, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 121 (by decide)))

theorem fz1_145_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨122, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 122 (by decide)))

theorem fz1_145_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨123, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 123 (by decide)))

theorem fz1_145_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨124, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 124 (by decide)))

theorem fz1_145_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨125, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 125 (by decide)))

theorem fz1_145_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨126, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 126 (by decide)))

theorem fz1_145_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨127, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 127 (by decide)))

theorem fz1_145_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨128, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 128 (by decide)))

theorem fz1_145_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨129, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 129 (by decide)))

theorem fz1_145_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨130, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 130 (by decide)))

theorem fz1_145_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨131, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 131 (by decide)))

theorem fz1_145_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨132, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 132 (by decide)))

theorem fz1_145_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨133, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 133 (by decide)))

theorem fz1_145_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨134, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 134 (by decide)))

theorem fz1_145_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨135, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 135 (by decide)))

theorem fz1_145_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨136, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 136 (by decide)))

theorem fz1_145_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨137, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 137 (by decide)))

theorem fz1_145_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨138, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 138 (by decide)))

theorem fz1_145_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨139, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 139 (by decide)))

theorem fz1_145_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨140, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 140 (by decide)))

theorem fz1_145_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨141, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 141 (by decide)))

theorem fz1_145_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨142, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 142 (by decide)))

theorem fz1_145_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨143, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 143 (by decide)))

theorem fz1_145_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨144, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 144 (by decide)))

theorem fz1_145_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK145)) = 0 :=
  repsFixedCard rK145 ⟨146, by decide⟩ R145 hpxR145 hcardq145
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_145) 146 (by decide)))

theorem fixz2_145 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 110, 111, 112, 113, 114, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK145) (retConj 2 (Q2.R145_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_145_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨1, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 1 (by decide)))

theorem fz2_145_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨2, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 2 (by decide)))

theorem fz2_145_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨3, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 3 (by decide)))

theorem fz2_145_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨4, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 4 (by decide)))

theorem fz2_145_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨5, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 5 (by decide)))

theorem fz2_145_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨6, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 6 (by decide)))

theorem fz2_145_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨7, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 7 (by decide)))

theorem fz2_145_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨8, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 8 (by decide)))

theorem fz2_145_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨9, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 9 (by decide)))

theorem fz2_145_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨13, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 13 (by decide)))

theorem fz2_145_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨14, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 14 (by decide)))

theorem fz2_145_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨15, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 15 (by decide)))

theorem fz2_145_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨16, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 16 (by decide)))

theorem fz2_145_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨17, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 17 (by decide)))

theorem fz2_145_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨18, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 18 (by decide)))

theorem fz2_145_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨19, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 19 (by decide)))

theorem fz2_145_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨20, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 20 (by decide)))

theorem fz2_145_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨21, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 21 (by decide)))

theorem fz2_145_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨22, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 22 (by decide)))

theorem fz2_145_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨23, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 23 (by decide)))

theorem fz2_145_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨24, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 24 (by decide)))

theorem fz2_145_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨25, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 25 (by decide)))

theorem fz2_145_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨26, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 26 (by decide)))

theorem fz2_145_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨27, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 27 (by decide)))

theorem fz2_145_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨28, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 28 (by decide)))

theorem fz2_145_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨29, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 29 (by decide)))

theorem fz2_145_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨30, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 30 (by decide)))

theorem fz2_145_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨31, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 31 (by decide)))

theorem fz2_145_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨32, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 32 (by decide)))

theorem fz2_145_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨33, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 33 (by decide)))

theorem fz2_145_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨34, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 34 (by decide)))

theorem fz2_145_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨35, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 35 (by decide)))

theorem fz2_145_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨36, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 36 (by decide)))

theorem fz2_145_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨37, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 37 (by decide)))

theorem fz2_145_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨38, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 38 (by decide)))

theorem fz2_145_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨39, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 39 (by decide)))

theorem fz2_145_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨40, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 40 (by decide)))

theorem fz2_145_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨41, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 41 (by decide)))

theorem fz2_145_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨42, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 42 (by decide)))

theorem fz2_145_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨48, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 48 (by decide)))

theorem fz2_145_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨49, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 49 (by decide)))

theorem fz2_145_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨50, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 50 (by decide)))

theorem fz2_145_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨51, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 51 (by decide)))

theorem fz2_145_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨52, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 52 (by decide)))

theorem fz2_145_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨55, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 55 (by decide)))

theorem fz2_145_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨56, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 56 (by decide)))

theorem fz2_145_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨57, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 57 (by decide)))

theorem fz2_145_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨58, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 58 (by decide)))

theorem fz2_145_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨59, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 59 (by decide)))

theorem fz2_145_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨60, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 60 (by decide)))

theorem fz2_145_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨61, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 61 (by decide)))

theorem fz2_145_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨62, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 62 (by decide)))

theorem fz2_145_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨63, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 63 (by decide)))

theorem fz2_145_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨64, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 64 (by decide)))

theorem fz2_145_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨65, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 65 (by decide)))

theorem fz2_145_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨66, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 66 (by decide)))

theorem fz2_145_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨67, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 67 (by decide)))

theorem fz2_145_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨68, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 68 (by decide)))

theorem fz2_145_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨69, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 69 (by decide)))

theorem fz2_145_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨70, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 70 (by decide)))

theorem fz2_145_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨71, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 71 (by decide)))

theorem fz2_145_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨72, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 72 (by decide)))

theorem fz2_145_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨73, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 73 (by decide)))

theorem fz2_145_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨74, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 74 (by decide)))

theorem fz2_145_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨75, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 75 (by decide)))

theorem fz2_145_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨76, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 76 (by decide)))

theorem fz2_145_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨77, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 77 (by decide)))

theorem fz2_145_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨78, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 78 (by decide)))

theorem fz2_145_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨79, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 79 (by decide)))

theorem fz2_145_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨80, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 80 (by decide)))

theorem fz2_145_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨81, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 81 (by decide)))

theorem fz2_145_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨82, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 82 (by decide)))

theorem fz2_145_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨83, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 83 (by decide)))

theorem fz2_145_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨84, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 84 (by decide)))

theorem fz2_145_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨85, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 85 (by decide)))

theorem fz2_145_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨86, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 86 (by decide)))

theorem fz2_145_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨87, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 87 (by decide)))

theorem fz2_145_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨88, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 88 (by decide)))

theorem fz2_145_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨89, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 89 (by decide)))

theorem fz2_145_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨90, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 90 (by decide)))

theorem fz2_145_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨91, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 91 (by decide)))

theorem fz2_145_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨92, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 92 (by decide)))

theorem fz2_145_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨93, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 93 (by decide)))

theorem fz2_145_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨94, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 94 (by decide)))

theorem fz2_145_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨95, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 95 (by decide)))

theorem fz2_145_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨96, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 96 (by decide)))

theorem fz2_145_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨97, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 97 (by decide)))

theorem fz2_145_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨98, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 98 (by decide)))

theorem fz2_145_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨99, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 99 (by decide)))

theorem fz2_145_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨100, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 100 (by decide)))

theorem fz2_145_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨101, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 101 (by decide)))

theorem fz2_145_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨102, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 102 (by decide)))

theorem fz2_145_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨103, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 103 (by decide)))

theorem fz2_145_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨104, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 104 (by decide)))

theorem fz2_145_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨110, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 110 (by decide)))

theorem fz2_145_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨111, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 111 (by decide)))

theorem fz2_145_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨112, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 112 (by decide)))

theorem fz2_145_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨113, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 113 (by decide)))

theorem fz2_145_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨114, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 114 (by decide)))

theorem fz2_145_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨116, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 116 (by decide)))

theorem fz2_145_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨117, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 117 (by decide)))

theorem fz2_145_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨118, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 118 (by decide)))

theorem fz2_145_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨119, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 119 (by decide)))

theorem fz2_145_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨120, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 120 (by decide)))

theorem fz2_145_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨121, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 121 (by decide)))

theorem fz2_145_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨122, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 122 (by decide)))

theorem fz2_145_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨123, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 123 (by decide)))

theorem fz2_145_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨124, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 124 (by decide)))

theorem fz2_145_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨125, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 125 (by decide)))

theorem fz2_145_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨126, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 126 (by decide)))

theorem fz2_145_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨127, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 127 (by decide)))

theorem fz2_145_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨128, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 128 (by decide)))

theorem fz2_145_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨129, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 129 (by decide)))

theorem fz2_145_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨130, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 130 (by decide)))

theorem fz2_145_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨131, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 131 (by decide)))

theorem fz2_145_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨132, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 132 (by decide)))

theorem fz2_145_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨133, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 133 (by decide)))

theorem fz2_145_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨134, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 134 (by decide)))

theorem fz2_145_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨135, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 135 (by decide)))

theorem fz2_145_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨136, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 136 (by decide)))

theorem fz2_145_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨137, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 137 (by decide)))

theorem fz2_145_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨138, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 138 (by decide)))

theorem fz2_145_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨139, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 139 (by decide)))

theorem fz2_145_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨140, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 140 (by decide)))

theorem fz2_145_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨141, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 141 (by decide)))

theorem fz2_145_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨142, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 142 (by decide)))

theorem fz2_145_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨143, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 143 (by decide)))

theorem fz2_145_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨144, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 144 (by decide)))

theorem fz2_145_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK145)) = 0 :=
  Q2.repsFixedCard2 rK145 ⟨146, by decide⟩ Q2.R145_2 Q2.hpxR145_2 Q2.hcardq145_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_145) 146 (by decide)))

theorem fixz1_146 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK146) (retConj 1 (R146 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_146_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨1, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 1 (by decide)))

theorem fz1_146_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨2, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 2 (by decide)))

theorem fz1_146_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨3, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 3 (by decide)))

theorem fz1_146_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨4, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 4 (by decide)))

theorem fz1_146_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨5, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 5 (by decide)))

theorem fz1_146_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨6, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 6 (by decide)))

theorem fz1_146_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨7, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 7 (by decide)))

theorem fz1_146_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨8, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 8 (by decide)))

theorem fz1_146_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨9, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 9 (by decide)))

theorem fz1_146_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨13, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 13 (by decide)))

theorem fz1_146_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨14, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 14 (by decide)))

theorem fz1_146_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨15, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 15 (by decide)))

theorem fz1_146_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨16, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 16 (by decide)))

theorem fz1_146_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨17, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 17 (by decide)))

theorem fz1_146_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨18, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 18 (by decide)))

theorem fz1_146_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨19, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 19 (by decide)))

theorem fz1_146_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨20, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 20 (by decide)))

theorem fz1_146_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨21, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 21 (by decide)))

theorem fz1_146_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨22, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 22 (by decide)))

theorem fz1_146_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨23, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 23 (by decide)))

theorem fz1_146_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨24, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 24 (by decide)))

theorem fz1_146_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨25, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 25 (by decide)))

theorem fz1_146_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨26, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 26 (by decide)))

theorem fz1_146_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨27, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 27 (by decide)))

theorem fz1_146_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨28, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 28 (by decide)))

theorem fz1_146_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨29, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 29 (by decide)))

theorem fz1_146_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨30, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 30 (by decide)))

theorem fz1_146_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨31, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 31 (by decide)))

theorem fz1_146_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨32, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 32 (by decide)))

theorem fz1_146_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨33, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 33 (by decide)))

theorem fz1_146_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨34, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 34 (by decide)))

theorem fz1_146_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨35, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 35 (by decide)))

theorem fz1_146_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨36, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 36 (by decide)))

theorem fz1_146_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨37, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 37 (by decide)))

theorem fz1_146_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨38, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 38 (by decide)))

theorem fz1_146_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨39, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 39 (by decide)))

theorem fz1_146_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨40, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 40 (by decide)))

theorem fz1_146_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨41, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 41 (by decide)))

theorem fz1_146_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨42, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 42 (by decide)))

theorem fz1_146_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨43, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 43 (by decide)))

theorem fz1_146_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨44, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 44 (by decide)))

theorem fz1_146_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨45, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 45 (by decide)))

theorem fz1_146_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨46, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 46 (by decide)))

theorem fz1_146_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨47, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 47 (by decide)))

theorem fz1_146_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨55, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 55 (by decide)))

theorem fz1_146_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨56, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 56 (by decide)))

theorem fz1_146_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨57, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 57 (by decide)))

theorem fz1_146_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨58, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 58 (by decide)))

theorem fz1_146_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨59, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 59 (by decide)))

theorem fz1_146_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨60, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 60 (by decide)))

theorem fz1_146_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨61, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 61 (by decide)))

theorem fz1_146_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨62, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 62 (by decide)))

theorem fz1_146_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨63, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 63 (by decide)))

theorem fz1_146_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨64, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 64 (by decide)))

theorem fz1_146_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨65, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 65 (by decide)))

theorem fz1_146_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨66, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 66 (by decide)))

theorem fz1_146_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨67, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 67 (by decide)))

theorem fz1_146_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨68, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 68 (by decide)))

theorem fz1_146_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨69, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 69 (by decide)))

theorem fz1_146_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨70, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 70 (by decide)))

theorem fz1_146_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨71, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 71 (by decide)))

theorem fz1_146_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨72, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 72 (by decide)))

theorem fz1_146_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨73, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 73 (by decide)))

theorem fz1_146_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨74, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 74 (by decide)))

theorem fz1_146_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨75, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 75 (by decide)))

theorem fz1_146_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨76, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 76 (by decide)))

theorem fz1_146_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨77, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 77 (by decide)))

theorem fz1_146_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨78, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 78 (by decide)))

theorem fz1_146_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨79, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 79 (by decide)))

theorem fz1_146_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨80, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 80 (by decide)))

theorem fz1_146_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨81, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 81 (by decide)))

theorem fz1_146_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨82, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 82 (by decide)))

theorem fz1_146_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨83, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 83 (by decide)))

theorem fz1_146_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨84, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 84 (by decide)))

theorem fz1_146_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨85, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 85 (by decide)))

theorem fz1_146_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨86, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 86 (by decide)))

theorem fz1_146_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨87, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 87 (by decide)))

theorem fz1_146_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨88, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 88 (by decide)))

theorem fz1_146_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨89, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 89 (by decide)))

theorem fz1_146_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨90, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 90 (by decide)))

theorem fz1_146_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨91, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 91 (by decide)))

theorem fz1_146_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨92, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 92 (by decide)))

theorem fz1_146_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨93, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 93 (by decide)))

theorem fz1_146_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨94, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 94 (by decide)))

theorem fz1_146_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨95, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 95 (by decide)))

theorem fz1_146_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨96, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 96 (by decide)))

theorem fz1_146_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨97, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 97 (by decide)))

theorem fz1_146_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨98, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 98 (by decide)))

theorem fz1_146_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨99, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 99 (by decide)))

theorem fz1_146_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨100, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 100 (by decide)))

theorem fz1_146_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨101, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 101 (by decide)))

theorem fz1_146_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨102, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 102 (by decide)))

theorem fz1_146_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨103, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 103 (by decide)))

theorem fz1_146_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨104, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 104 (by decide)))

theorem fz1_146_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨105, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 105 (by decide)))

theorem fz1_146_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨106, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 106 (by decide)))

theorem fz1_146_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨107, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 107 (by decide)))

theorem fz1_146_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨108, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 108 (by decide)))

theorem fz1_146_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨109, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 109 (by decide)))

theorem fz1_146_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨116, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 116 (by decide)))

theorem fz1_146_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨117, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 117 (by decide)))

theorem fz1_146_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨118, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 118 (by decide)))

theorem fz1_146_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨119, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 119 (by decide)))

theorem fz1_146_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨120, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 120 (by decide)))

theorem fz1_146_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨121, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 121 (by decide)))

theorem fz1_146_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨122, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 122 (by decide)))

theorem fz1_146_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨123, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 123 (by decide)))

theorem fz1_146_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨124, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 124 (by decide)))

theorem fz1_146_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨125, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 125 (by decide)))

theorem fz1_146_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨126, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 126 (by decide)))

theorem fz1_146_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨127, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 127 (by decide)))

theorem fz1_146_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨128, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 128 (by decide)))

theorem fz1_146_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨129, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 129 (by decide)))

theorem fz1_146_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨130, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 130 (by decide)))

theorem fz1_146_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨131, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 131 (by decide)))

theorem fz1_146_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨132, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 132 (by decide)))

theorem fz1_146_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨133, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 133 (by decide)))

theorem fz1_146_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨134, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 134 (by decide)))

theorem fz1_146_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨135, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 135 (by decide)))

theorem fz1_146_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨136, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 136 (by decide)))

theorem fz1_146_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨137, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 137 (by decide)))

theorem fz1_146_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨138, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 138 (by decide)))

theorem fz1_146_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨139, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 139 (by decide)))

theorem fz1_146_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨140, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 140 (by decide)))

theorem fz1_146_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨141, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 141 (by decide)))

theorem fz1_146_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨142, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 142 (by decide)))

theorem fz1_146_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨143, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 143 (by decide)))

theorem fz1_146_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨144, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 144 (by decide)))

theorem fz1_146_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK146)) = 0 :=
  repsFixedCard rK146 ⟨145, by decide⟩ R146 hpxR146 hcardq146
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_146) 145 (by decide)))

theorem fixz2_146 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK146) (retConj 2 (Q2.R146_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_146_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨1, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 1 (by decide)))

theorem fz2_146_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨2, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 2 (by decide)))

theorem fz2_146_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨3, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 3 (by decide)))

theorem fz2_146_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨4, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 4 (by decide)))

theorem fz2_146_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨5, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 5 (by decide)))

theorem fz2_146_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨6, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 6 (by decide)))

theorem fz2_146_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨7, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 7 (by decide)))

theorem fz2_146_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨8, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 8 (by decide)))

theorem fz2_146_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨9, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 9 (by decide)))

theorem fz2_146_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨13, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 13 (by decide)))

theorem fz2_146_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨14, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 14 (by decide)))

theorem fz2_146_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨15, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 15 (by decide)))

theorem fz2_146_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨16, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 16 (by decide)))

theorem fz2_146_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨17, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 17 (by decide)))

theorem fz2_146_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨18, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 18 (by decide)))

theorem fz2_146_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨19, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 19 (by decide)))

theorem fz2_146_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨20, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 20 (by decide)))

theorem fz2_146_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨21, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 21 (by decide)))

theorem fz2_146_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨22, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 22 (by decide)))

theorem fz2_146_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨23, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 23 (by decide)))

theorem fz2_146_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨24, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 24 (by decide)))

theorem fz2_146_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨25, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 25 (by decide)))

theorem fz2_146_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨26, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 26 (by decide)))

theorem fz2_146_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨27, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 27 (by decide)))

theorem fz2_146_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨28, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 28 (by decide)))

theorem fz2_146_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨29, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 29 (by decide)))

theorem fz2_146_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨30, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 30 (by decide)))

theorem fz2_146_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨31, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 31 (by decide)))

theorem fz2_146_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨32, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 32 (by decide)))

theorem fz2_146_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨33, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 33 (by decide)))

theorem fz2_146_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨34, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 34 (by decide)))

theorem fz2_146_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨35, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 35 (by decide)))

theorem fz2_146_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨36, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 36 (by decide)))

theorem fz2_146_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨37, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 37 (by decide)))

theorem fz2_146_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨38, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 38 (by decide)))

theorem fz2_146_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨39, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 39 (by decide)))

theorem fz2_146_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨40, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 40 (by decide)))

theorem fz2_146_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨41, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 41 (by decide)))

theorem fz2_146_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨42, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 42 (by decide)))

theorem fz2_146_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨43, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 43 (by decide)))

theorem fz2_146_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨44, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 44 (by decide)))

theorem fz2_146_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨45, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 45 (by decide)))

theorem fz2_146_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨46, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 46 (by decide)))

theorem fz2_146_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨47, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 47 (by decide)))

theorem fz2_146_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨55, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 55 (by decide)))

theorem fz2_146_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨56, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 56 (by decide)))

theorem fz2_146_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨57, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 57 (by decide)))

theorem fz2_146_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨58, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 58 (by decide)))

theorem fz2_146_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨59, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 59 (by decide)))

theorem fz2_146_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨60, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 60 (by decide)))

theorem fz2_146_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨61, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 61 (by decide)))

theorem fz2_146_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨62, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 62 (by decide)))

theorem fz2_146_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨63, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 63 (by decide)))

theorem fz2_146_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨64, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 64 (by decide)))

theorem fz2_146_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨65, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 65 (by decide)))

theorem fz2_146_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨66, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 66 (by decide)))

theorem fz2_146_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨67, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 67 (by decide)))

theorem fz2_146_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨68, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 68 (by decide)))

theorem fz2_146_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨69, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 69 (by decide)))

theorem fz2_146_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨70, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 70 (by decide)))

theorem fz2_146_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨71, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 71 (by decide)))

theorem fz2_146_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨72, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 72 (by decide)))

theorem fz2_146_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨73, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 73 (by decide)))

theorem fz2_146_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨74, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 74 (by decide)))

theorem fz2_146_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨75, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 75 (by decide)))

theorem fz2_146_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨76, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 76 (by decide)))

theorem fz2_146_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨77, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 77 (by decide)))

theorem fz2_146_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨78, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 78 (by decide)))

theorem fz2_146_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨79, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 79 (by decide)))

theorem fz2_146_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨80, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 80 (by decide)))

theorem fz2_146_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨81, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 81 (by decide)))

theorem fz2_146_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨82, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 82 (by decide)))

theorem fz2_146_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨83, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 83 (by decide)))

theorem fz2_146_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨84, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 84 (by decide)))

theorem fz2_146_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨85, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 85 (by decide)))

theorem fz2_146_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨86, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 86 (by decide)))

theorem fz2_146_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨87, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 87 (by decide)))

theorem fz2_146_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨88, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 88 (by decide)))

theorem fz2_146_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨89, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 89 (by decide)))

theorem fz2_146_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨90, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 90 (by decide)))

theorem fz2_146_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨91, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 91 (by decide)))

theorem fz2_146_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨92, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 92 (by decide)))

theorem fz2_146_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨93, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 93 (by decide)))

theorem fz2_146_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨94, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 94 (by decide)))

theorem fz2_146_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨95, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 95 (by decide)))

theorem fz2_146_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨96, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 96 (by decide)))

theorem fz2_146_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨97, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 97 (by decide)))

theorem fz2_146_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨98, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 98 (by decide)))

theorem fz2_146_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨99, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 99 (by decide)))

theorem fz2_146_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨100, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 100 (by decide)))

theorem fz2_146_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨101, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 101 (by decide)))

theorem fz2_146_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨102, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 102 (by decide)))

theorem fz2_146_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨103, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 103 (by decide)))

theorem fz2_146_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨104, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 104 (by decide)))

theorem fz2_146_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨105, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 105 (by decide)))

theorem fz2_146_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨106, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 106 (by decide)))

theorem fz2_146_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨107, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 107 (by decide)))

theorem fz2_146_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨108, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 108 (by decide)))

theorem fz2_146_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨109, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 109 (by decide)))

theorem fz2_146_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨116, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 116 (by decide)))

theorem fz2_146_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨117, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 117 (by decide)))

theorem fz2_146_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨118, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 118 (by decide)))

theorem fz2_146_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨119, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 119 (by decide)))

theorem fz2_146_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨120, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 120 (by decide)))

theorem fz2_146_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨121, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 121 (by decide)))

theorem fz2_146_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨122, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 122 (by decide)))

theorem fz2_146_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨123, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 123 (by decide)))

theorem fz2_146_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨124, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 124 (by decide)))

theorem fz2_146_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨125, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 125 (by decide)))

theorem fz2_146_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨126, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 126 (by decide)))

theorem fz2_146_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨127, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 127 (by decide)))

theorem fz2_146_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨128, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 128 (by decide)))

theorem fz2_146_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨129, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 129 (by decide)))

theorem fz2_146_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨130, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 130 (by decide)))

theorem fz2_146_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨131, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 131 (by decide)))

theorem fz2_146_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨132, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 132 (by decide)))

theorem fz2_146_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨133, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 133 (by decide)))

theorem fz2_146_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨134, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 134 (by decide)))

theorem fz2_146_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨135, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 135 (by decide)))

theorem fz2_146_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨136, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 136 (by decide)))

theorem fz2_146_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨137, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 137 (by decide)))

theorem fz2_146_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨138, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 138 (by decide)))

theorem fz2_146_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨139, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 139 (by decide)))

theorem fz2_146_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨140, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 140 (by decide)))

theorem fz2_146_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨141, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 141 (by decide)))

theorem fz2_146_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨142, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 142 (by decide)))

theorem fz2_146_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨143, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 143 (by decide)))

theorem fz2_146_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨144, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 144 (by decide)))

theorem fz2_146_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK146)) = 0 :=
  Q2.repsFixedCard2 rK146 ⟨145, by decide⟩ Q2.R146_2 Q2.hpxR146_2 Q2.hcardq146_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_146) 145 (by decide)))

end LeanDring.P5Presentation
