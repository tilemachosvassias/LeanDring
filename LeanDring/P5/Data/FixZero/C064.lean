/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C017

/-!
# Species-table cells, off-support emptiness certificates, chunk 63

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

theorem fixz1_73 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK73) (retConj 1 (R73 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_73_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨1, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 1 (by decide)))

theorem fz1_73_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨2, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 2 (by decide)))

theorem fz1_73_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨3, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 3 (by decide)))

theorem fz1_73_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨4, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 4 (by decide)))

theorem fz1_73_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨5, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 5 (by decide)))

theorem fz1_73_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨7, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 7 (by decide)))

theorem fz1_73_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨8, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 8 (by decide)))

theorem fz1_73_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨9, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 9 (by decide)))

theorem fz1_73_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨10, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 10 (by decide)))

theorem fz1_73_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨11, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 11 (by decide)))

theorem fz1_73_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨13, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 13 (by decide)))

theorem fz1_73_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨14, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 14 (by decide)))

theorem fz1_73_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨15, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 15 (by decide)))

theorem fz1_73_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨16, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 16 (by decide)))

theorem fz1_73_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨17, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 17 (by decide)))

theorem fz1_73_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨18, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 18 (by decide)))

theorem fz1_73_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨19, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 19 (by decide)))

theorem fz1_73_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨20, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 20 (by decide)))

theorem fz1_73_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨21, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 21 (by decide)))

theorem fz1_73_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨22, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 22 (by decide)))

theorem fz1_73_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨23, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 23 (by decide)))

theorem fz1_73_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨25, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 25 (by decide)))

theorem fz1_73_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨26, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 26 (by decide)))

theorem fz1_73_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨27, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 27 (by decide)))

theorem fz1_73_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨28, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 28 (by decide)))

theorem fz1_73_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨29, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 29 (by decide)))

theorem fz1_73_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨30, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 30 (by decide)))

theorem fz1_73_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨32, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 32 (by decide)))

theorem fz1_73_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨33, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 33 (by decide)))

theorem fz1_73_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨34, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 34 (by decide)))

theorem fz1_73_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨35, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 35 (by decide)))

theorem fz1_73_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨37, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 37 (by decide)))

theorem fz1_73_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨38, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 38 (by decide)))

theorem fz1_73_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨39, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 39 (by decide)))

theorem fz1_73_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨40, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 40 (by decide)))

theorem fz1_73_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨42, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 42 (by decide)))

theorem fz1_73_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨43, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 43 (by decide)))

theorem fz1_73_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨44, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 44 (by decide)))

theorem fz1_73_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨45, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 45 (by decide)))

theorem fz1_73_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨47, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 47 (by decide)))

theorem fz1_73_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨48, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 48 (by decide)))

theorem fz1_73_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨49, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 49 (by decide)))

theorem fz1_73_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨50, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 50 (by decide)))

theorem fz1_73_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨52, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 52 (by decide)))

theorem fz1_73_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨53, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 53 (by decide)))

theorem fz1_73_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨54, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 54 (by decide)))

theorem fz1_73_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨55, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 55 (by decide)))

theorem fz1_73_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨56, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 56 (by decide)))

theorem fz1_73_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨57, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 57 (by decide)))

theorem fz1_73_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨58, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 58 (by decide)))

theorem fz1_73_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨59, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 59 (by decide)))

theorem fz1_73_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨60, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 60 (by decide)))

theorem fz1_73_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨61, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 61 (by decide)))

theorem fz1_73_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨62, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 62 (by decide)))

theorem fz1_73_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨63, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 63 (by decide)))

theorem fz1_73_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨64, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 64 (by decide)))

theorem fz1_73_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨65, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 65 (by decide)))

theorem fz1_73_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨66, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 66 (by decide)))

theorem fz1_73_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨67, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 67 (by decide)))

theorem fz1_73_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨68, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 68 (by decide)))

theorem fz1_73_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨69, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 69 (by decide)))

theorem fz1_73_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨70, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 70 (by decide)))

theorem fz1_73_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨71, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 71 (by decide)))

theorem fz1_73_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨72, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 72 (by decide)))

theorem fz1_73_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨74, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 74 (by decide)))

theorem fz1_73_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨75, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 75 (by decide)))

theorem fz1_73_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨76, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 76 (by decide)))

theorem fz1_73_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨77, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 77 (by decide)))

theorem fz1_73_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨78, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 78 (by decide)))

theorem fz1_73_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨79, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 79 (by decide)))

theorem fz1_73_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨80, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 80 (by decide)))

theorem fz1_73_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨81, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 81 (by decide)))

theorem fz1_73_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨82, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 82 (by decide)))

theorem fz1_73_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨83, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 83 (by decide)))

theorem fz1_73_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨84, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 84 (by decide)))

theorem fz1_73_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨85, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 85 (by decide)))

theorem fz1_73_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨86, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 86 (by decide)))

theorem fz1_73_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨87, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 87 (by decide)))

theorem fz1_73_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨88, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 88 (by decide)))

theorem fz1_73_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨89, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 89 (by decide)))

theorem fz1_73_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨90, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 90 (by decide)))

theorem fz1_73_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨91, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 91 (by decide)))

theorem fz1_73_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨92, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 92 (by decide)))

theorem fz1_73_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨93, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 93 (by decide)))

theorem fz1_73_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨94, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 94 (by decide)))

theorem fz1_73_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨95, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 95 (by decide)))

theorem fz1_73_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨96, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 96 (by decide)))

theorem fz1_73_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨97, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 97 (by decide)))

theorem fz1_73_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨98, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 98 (by decide)))

theorem fz1_73_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨99, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 99 (by decide)))

theorem fz1_73_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨100, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 100 (by decide)))

theorem fz1_73_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨101, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 101 (by decide)))

theorem fz1_73_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨102, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 102 (by decide)))

theorem fz1_73_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨103, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 103 (by decide)))

theorem fz1_73_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨104, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 104 (by decide)))

theorem fz1_73_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨105, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 105 (by decide)))

theorem fz1_73_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨106, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 106 (by decide)))

theorem fz1_73_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨107, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 107 (by decide)))

theorem fz1_73_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨108, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 108 (by decide)))

theorem fz1_73_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨109, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 109 (by decide)))

theorem fz1_73_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨110, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 110 (by decide)))

theorem fz1_73_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨111, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 111 (by decide)))

theorem fz1_73_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨112, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 112 (by decide)))

theorem fz1_73_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨113, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 113 (by decide)))

theorem fz1_73_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨114, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 114 (by decide)))

theorem fz1_73_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK73)) = 0 :=
  repsFixedCard rK73 ⟨115, by decide⟩ R73 hpxR73 hcardq73
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_73) 115 (by decide)))

theorem fixz2_73 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK73) (retConj 2 (Q2.R73_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_73_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨1, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 1 (by decide)))

theorem fz2_73_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨2, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 2 (by decide)))

theorem fz2_73_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨3, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 3 (by decide)))

theorem fz2_73_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨4, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 4 (by decide)))

theorem fz2_73_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨5, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 5 (by decide)))

theorem fz2_73_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨7, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 7 (by decide)))

theorem fz2_73_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨8, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 8 (by decide)))

theorem fz2_73_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨9, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 9 (by decide)))

theorem fz2_73_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨10, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 10 (by decide)))

theorem fz2_73_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨11, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 11 (by decide)))

theorem fz2_73_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨13, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 13 (by decide)))

theorem fz2_73_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨14, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 14 (by decide)))

theorem fz2_73_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨15, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 15 (by decide)))

theorem fz2_73_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨16, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 16 (by decide)))

theorem fz2_73_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨17, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 17 (by decide)))

theorem fz2_73_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨18, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 18 (by decide)))

theorem fz2_73_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨19, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 19 (by decide)))

theorem fz2_73_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨20, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 20 (by decide)))

theorem fz2_73_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨21, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 21 (by decide)))

theorem fz2_73_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨22, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 22 (by decide)))

theorem fz2_73_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨23, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 23 (by decide)))

theorem fz2_73_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨25, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 25 (by decide)))

theorem fz2_73_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨26, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 26 (by decide)))

theorem fz2_73_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨27, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 27 (by decide)))

theorem fz2_73_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨28, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 28 (by decide)))

theorem fz2_73_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨29, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 29 (by decide)))

theorem fz2_73_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨30, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 30 (by decide)))

theorem fz2_73_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨32, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 32 (by decide)))

theorem fz2_73_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨33, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 33 (by decide)))

theorem fz2_73_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨34, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 34 (by decide)))

theorem fz2_73_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨35, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 35 (by decide)))

theorem fz2_73_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨37, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 37 (by decide)))

theorem fz2_73_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨38, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 38 (by decide)))

theorem fz2_73_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨39, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 39 (by decide)))

theorem fz2_73_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨40, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 40 (by decide)))

theorem fz2_73_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨42, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 42 (by decide)))

theorem fz2_73_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨43, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 43 (by decide)))

theorem fz2_73_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨44, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 44 (by decide)))

theorem fz2_73_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨45, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 45 (by decide)))

theorem fz2_73_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨47, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 47 (by decide)))

theorem fz2_73_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨48, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 48 (by decide)))

theorem fz2_73_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨49, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 49 (by decide)))

theorem fz2_73_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨50, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 50 (by decide)))

theorem fz2_73_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨52, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 52 (by decide)))

theorem fz2_73_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨53, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 53 (by decide)))

theorem fz2_73_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨54, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 54 (by decide)))

theorem fz2_73_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨55, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 55 (by decide)))

theorem fz2_73_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨56, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 56 (by decide)))

theorem fz2_73_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨57, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 57 (by decide)))

theorem fz2_73_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨58, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 58 (by decide)))

theorem fz2_73_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨59, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 59 (by decide)))

theorem fz2_73_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨60, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 60 (by decide)))

theorem fz2_73_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨61, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 61 (by decide)))

theorem fz2_73_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨62, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 62 (by decide)))

theorem fz2_73_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨63, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 63 (by decide)))

theorem fz2_73_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨64, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 64 (by decide)))

theorem fz2_73_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨65, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 65 (by decide)))

theorem fz2_73_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨66, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 66 (by decide)))

theorem fz2_73_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨67, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 67 (by decide)))

theorem fz2_73_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨68, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 68 (by decide)))

theorem fz2_73_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨69, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 69 (by decide)))

theorem fz2_73_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨70, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 70 (by decide)))

theorem fz2_73_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨71, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 71 (by decide)))

theorem fz2_73_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨72, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 72 (by decide)))

theorem fz2_73_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨74, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 74 (by decide)))

theorem fz2_73_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨75, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 75 (by decide)))

theorem fz2_73_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨76, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 76 (by decide)))

theorem fz2_73_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨77, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 77 (by decide)))

theorem fz2_73_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨78, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 78 (by decide)))

theorem fz2_73_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨79, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 79 (by decide)))

theorem fz2_73_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨80, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 80 (by decide)))

theorem fz2_73_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨81, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 81 (by decide)))

theorem fz2_73_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨82, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 82 (by decide)))

theorem fz2_73_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨83, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 83 (by decide)))

theorem fz2_73_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨84, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 84 (by decide)))

theorem fz2_73_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨85, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 85 (by decide)))

theorem fz2_73_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨86, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 86 (by decide)))

theorem fz2_73_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨87, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 87 (by decide)))

theorem fz2_73_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨88, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 88 (by decide)))

theorem fz2_73_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨89, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 89 (by decide)))

theorem fz2_73_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨90, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 90 (by decide)))

theorem fz2_73_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨91, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 91 (by decide)))

theorem fz2_73_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨92, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 92 (by decide)))

theorem fz2_73_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨93, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 93 (by decide)))

theorem fz2_73_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨94, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 94 (by decide)))

theorem fz2_73_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨95, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 95 (by decide)))

theorem fz2_73_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨96, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 96 (by decide)))

theorem fz2_73_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨97, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 97 (by decide)))

theorem fz2_73_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨98, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 98 (by decide)))

theorem fz2_73_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨99, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 99 (by decide)))

theorem fz2_73_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨100, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 100 (by decide)))

theorem fz2_73_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨101, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 101 (by decide)))

theorem fz2_73_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨102, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 102 (by decide)))

theorem fz2_73_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨103, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 103 (by decide)))

theorem fz2_73_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨104, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 104 (by decide)))

theorem fz2_73_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨105, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 105 (by decide)))

theorem fz2_73_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨106, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 106 (by decide)))

theorem fz2_73_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨107, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 107 (by decide)))

theorem fz2_73_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨108, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 108 (by decide)))

theorem fz2_73_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨109, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 109 (by decide)))

theorem fz2_73_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨110, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 110 (by decide)))

theorem fz2_73_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨111, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 111 (by decide)))

theorem fz2_73_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨112, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 112 (by decide)))

theorem fz2_73_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨113, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 113 (by decide)))

theorem fz2_73_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨114, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 114 (by decide)))

theorem fz2_73_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK73)) = 0 :=
  Q2.repsFixedCard2 rK73 ⟨115, by decide⟩ Q2.R73_2 Q2.hpxR73_2 Q2.hcardq73_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_73) 115 (by decide)))

theorem fixz1_74 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK74) (retConj 1 (R74 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_74_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨1, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 1 (by decide)))

theorem fz1_74_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨2, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 2 (by decide)))

theorem fz1_74_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨3, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 3 (by decide)))

theorem fz1_74_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨4, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 4 (by decide)))

theorem fz1_74_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨5, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 5 (by decide)))

theorem fz1_74_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨6, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 6 (by decide)))

theorem fz1_74_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨7, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 7 (by decide)))

theorem fz1_74_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨9, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 9 (by decide)))

theorem fz1_74_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨10, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 10 (by decide)))

theorem fz1_74_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨11, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 11 (by decide)))

theorem fz1_74_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨13, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 13 (by decide)))

theorem fz1_74_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨14, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 14 (by decide)))

theorem fz1_74_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨15, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 15 (by decide)))

theorem fz1_74_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨16, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 16 (by decide)))

theorem fz1_74_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨17, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 17 (by decide)))

theorem fz1_74_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨18, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 18 (by decide)))

theorem fz1_74_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨19, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 19 (by decide)))

theorem fz1_74_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨20, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 20 (by decide)))

theorem fz1_74_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨21, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 21 (by decide)))

theorem fz1_74_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨22, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 22 (by decide)))

theorem fz1_74_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨23, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 23 (by decide)))

theorem fz1_74_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨24, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 24 (by decide)))

theorem fz1_74_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨25, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 25 (by decide)))

theorem fz1_74_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨27, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 27 (by decide)))

theorem fz1_74_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨28, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 28 (by decide)))

theorem fz1_74_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨29, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 29 (by decide)))

theorem fz1_74_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨30, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 30 (by decide)))

theorem fz1_74_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨32, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 32 (by decide)))

theorem fz1_74_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨33, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 33 (by decide)))

theorem fz1_74_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨34, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 34 (by decide)))

theorem fz1_74_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨35, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 35 (by decide)))

theorem fz1_74_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨37, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 37 (by decide)))

theorem fz1_74_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨38, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 38 (by decide)))

theorem fz1_74_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨39, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 39 (by decide)))

theorem fz1_74_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨40, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 40 (by decide)))

theorem fz1_74_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨42, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 42 (by decide)))

theorem fz1_74_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨43, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 43 (by decide)))

theorem fz1_74_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨44, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 44 (by decide)))

theorem fz1_74_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨45, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 45 (by decide)))

theorem fz1_74_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨47, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 47 (by decide)))

theorem fz1_74_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨48, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 48 (by decide)))

theorem fz1_74_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨49, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 49 (by decide)))

theorem fz1_74_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨50, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 50 (by decide)))

theorem fz1_74_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨52, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 52 (by decide)))

theorem fz1_74_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨53, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 53 (by decide)))

theorem fz1_74_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨54, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 54 (by decide)))

theorem fz1_74_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨55, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 55 (by decide)))

theorem fz1_74_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨56, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 56 (by decide)))

theorem fz1_74_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨57, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 57 (by decide)))

theorem fz1_74_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨58, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 58 (by decide)))

theorem fz1_74_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨59, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 59 (by decide)))

theorem fz1_74_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨60, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 60 (by decide)))

theorem fz1_74_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨61, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 61 (by decide)))

theorem fz1_74_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨62, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 62 (by decide)))

theorem fz1_74_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨63, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 63 (by decide)))

theorem fz1_74_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨64, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 64 (by decide)))

theorem fz1_74_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨65, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 65 (by decide)))

theorem fz1_74_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨66, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 66 (by decide)))

theorem fz1_74_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨67, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 67 (by decide)))

theorem fz1_74_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨68, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 68 (by decide)))

theorem fz1_74_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨69, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 69 (by decide)))

theorem fz1_74_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨70, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 70 (by decide)))

theorem fz1_74_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨71, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 71 (by decide)))

theorem fz1_74_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨72, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 72 (by decide)))

theorem fz1_74_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨73, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 73 (by decide)))

theorem fz1_74_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨75, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 75 (by decide)))

theorem fz1_74_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨76, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 76 (by decide)))

theorem fz1_74_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨77, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 77 (by decide)))

theorem fz1_74_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨78, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 78 (by decide)))

theorem fz1_74_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨79, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 79 (by decide)))

theorem fz1_74_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨80, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 80 (by decide)))

theorem fz1_74_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨81, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 81 (by decide)))

theorem fz1_74_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨82, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 82 (by decide)))

theorem fz1_74_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨83, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 83 (by decide)))

theorem fz1_74_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨84, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 84 (by decide)))

theorem fz1_74_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨85, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 85 (by decide)))

theorem fz1_74_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨86, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 86 (by decide)))

theorem fz1_74_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨87, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 87 (by decide)))

theorem fz1_74_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨88, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 88 (by decide)))

theorem fz1_74_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨89, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 89 (by decide)))

theorem fz1_74_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨90, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 90 (by decide)))

theorem fz1_74_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨91, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 91 (by decide)))

theorem fz1_74_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨92, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 92 (by decide)))

theorem fz1_74_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨93, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 93 (by decide)))

theorem fz1_74_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨94, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 94 (by decide)))

theorem fz1_74_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨95, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 95 (by decide)))

theorem fz1_74_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨96, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 96 (by decide)))

theorem fz1_74_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨97, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 97 (by decide)))

theorem fz1_74_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨98, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 98 (by decide)))

theorem fz1_74_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨99, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 99 (by decide)))

theorem fz1_74_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨100, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 100 (by decide)))

theorem fz1_74_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨101, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 101 (by decide)))

theorem fz1_74_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨102, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 102 (by decide)))

theorem fz1_74_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨103, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 103 (by decide)))

theorem fz1_74_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨104, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 104 (by decide)))

theorem fz1_74_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨105, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 105 (by decide)))

theorem fz1_74_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨106, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 106 (by decide)))

theorem fz1_74_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨107, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 107 (by decide)))

theorem fz1_74_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨108, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 108 (by decide)))

theorem fz1_74_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨109, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 109 (by decide)))

theorem fz1_74_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨110, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 110 (by decide)))

theorem fz1_74_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨111, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 111 (by decide)))

theorem fz1_74_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨112, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 112 (by decide)))

theorem fz1_74_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨113, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 113 (by decide)))

theorem fz1_74_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨114, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 114 (by decide)))

theorem fz1_74_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK74)) = 0 :=
  repsFixedCard rK74 ⟨115, by decide⟩ R74 hpxR74 hcardq74
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_74) 115 (by decide)))

theorem fixz2_74 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK74) (retConj 2 (Q2.R74_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_74_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨1, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 1 (by decide)))

theorem fz2_74_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨2, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 2 (by decide)))

theorem fz2_74_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨3, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 3 (by decide)))

theorem fz2_74_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨4, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 4 (by decide)))

theorem fz2_74_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨5, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 5 (by decide)))

theorem fz2_74_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨6, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 6 (by decide)))

theorem fz2_74_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨7, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 7 (by decide)))

theorem fz2_74_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨9, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 9 (by decide)))

theorem fz2_74_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨10, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 10 (by decide)))

theorem fz2_74_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨11, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 11 (by decide)))

theorem fz2_74_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨13, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 13 (by decide)))

theorem fz2_74_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨14, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 14 (by decide)))

theorem fz2_74_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨15, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 15 (by decide)))

theorem fz2_74_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨16, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 16 (by decide)))

theorem fz2_74_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨17, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 17 (by decide)))

theorem fz2_74_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨18, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 18 (by decide)))

theorem fz2_74_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨19, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 19 (by decide)))

theorem fz2_74_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨20, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 20 (by decide)))

theorem fz2_74_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨21, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 21 (by decide)))

theorem fz2_74_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨22, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 22 (by decide)))

theorem fz2_74_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨23, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 23 (by decide)))

theorem fz2_74_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨24, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 24 (by decide)))

theorem fz2_74_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨25, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 25 (by decide)))

theorem fz2_74_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨27, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 27 (by decide)))

theorem fz2_74_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨28, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 28 (by decide)))

theorem fz2_74_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨29, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 29 (by decide)))

theorem fz2_74_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨30, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 30 (by decide)))

theorem fz2_74_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨32, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 32 (by decide)))

theorem fz2_74_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨33, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 33 (by decide)))

theorem fz2_74_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨34, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 34 (by decide)))

theorem fz2_74_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨35, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 35 (by decide)))

theorem fz2_74_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨37, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 37 (by decide)))

theorem fz2_74_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨38, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 38 (by decide)))

theorem fz2_74_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨39, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 39 (by decide)))

theorem fz2_74_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨40, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 40 (by decide)))

theorem fz2_74_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨42, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 42 (by decide)))

theorem fz2_74_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨43, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 43 (by decide)))

theorem fz2_74_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨44, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 44 (by decide)))

theorem fz2_74_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨45, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 45 (by decide)))

theorem fz2_74_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨47, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 47 (by decide)))

theorem fz2_74_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨48, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 48 (by decide)))

theorem fz2_74_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨49, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 49 (by decide)))

theorem fz2_74_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨50, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 50 (by decide)))

theorem fz2_74_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨52, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 52 (by decide)))

theorem fz2_74_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨53, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 53 (by decide)))

theorem fz2_74_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨54, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 54 (by decide)))

theorem fz2_74_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨55, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 55 (by decide)))

theorem fz2_74_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨56, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 56 (by decide)))

theorem fz2_74_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨57, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 57 (by decide)))

theorem fz2_74_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨58, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 58 (by decide)))

theorem fz2_74_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨59, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 59 (by decide)))

theorem fz2_74_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨60, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 60 (by decide)))

theorem fz2_74_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨61, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 61 (by decide)))

theorem fz2_74_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨62, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 62 (by decide)))

theorem fz2_74_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨63, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 63 (by decide)))

theorem fz2_74_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨64, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 64 (by decide)))

theorem fz2_74_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨65, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 65 (by decide)))

theorem fz2_74_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨66, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 66 (by decide)))

theorem fz2_74_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨67, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 67 (by decide)))

theorem fz2_74_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨68, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 68 (by decide)))

theorem fz2_74_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨69, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 69 (by decide)))

theorem fz2_74_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨70, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 70 (by decide)))

theorem fz2_74_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨71, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 71 (by decide)))

theorem fz2_74_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨72, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 72 (by decide)))

theorem fz2_74_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨73, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 73 (by decide)))

theorem fz2_74_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨75, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 75 (by decide)))

theorem fz2_74_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨76, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 76 (by decide)))

theorem fz2_74_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨77, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 77 (by decide)))

theorem fz2_74_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨78, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 78 (by decide)))

theorem fz2_74_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨79, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 79 (by decide)))

theorem fz2_74_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨80, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 80 (by decide)))

theorem fz2_74_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨81, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 81 (by decide)))

theorem fz2_74_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨82, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 82 (by decide)))

theorem fz2_74_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨83, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 83 (by decide)))

theorem fz2_74_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨84, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 84 (by decide)))

theorem fz2_74_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨85, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 85 (by decide)))

theorem fz2_74_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨86, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 86 (by decide)))

theorem fz2_74_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨87, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 87 (by decide)))

theorem fz2_74_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨88, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 88 (by decide)))

theorem fz2_74_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨89, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 89 (by decide)))

theorem fz2_74_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨90, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 90 (by decide)))

theorem fz2_74_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨91, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 91 (by decide)))

theorem fz2_74_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨92, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 92 (by decide)))

theorem fz2_74_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨93, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 93 (by decide)))

theorem fz2_74_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨94, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 94 (by decide)))

theorem fz2_74_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨95, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 95 (by decide)))

theorem fz2_74_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨96, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 96 (by decide)))

theorem fz2_74_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨97, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 97 (by decide)))

theorem fz2_74_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨98, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 98 (by decide)))

theorem fz2_74_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨99, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 99 (by decide)))

theorem fz2_74_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨100, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 100 (by decide)))

theorem fz2_74_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨101, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 101 (by decide)))

theorem fz2_74_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨102, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 102 (by decide)))

theorem fz2_74_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨103, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 103 (by decide)))

theorem fz2_74_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨104, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 104 (by decide)))

theorem fz2_74_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨105, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 105 (by decide)))

theorem fz2_74_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨106, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 106 (by decide)))

theorem fz2_74_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨107, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 107 (by decide)))

theorem fz2_74_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨108, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 108 (by decide)))

theorem fz2_74_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨109, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 109 (by decide)))

theorem fz2_74_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨110, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 110 (by decide)))

theorem fz2_74_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨111, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 111 (by decide)))

theorem fz2_74_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨112, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 112 (by decide)))

theorem fz2_74_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨113, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 113 (by decide)))

theorem fz2_74_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨114, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 114 (by decide)))

theorem fz2_74_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK74)) = 0 :=
  Q2.repsFixedCard2 rK74 ⟨115, by decide⟩ Q2.R74_2 Q2.hpxR74_2 Q2.hcardq74_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_74) 115 (by decide)))

end LeanDring.P5Presentation
