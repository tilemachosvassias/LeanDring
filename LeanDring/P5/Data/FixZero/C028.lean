/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C016

/-!
# Species-table cells, off-support emptiness certificates, chunk 27

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

theorem fixz1_28 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK28) (retConj 1 (R28 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_28_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨1, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 1 (by decide)))

theorem fz1_28_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨2, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 2 (by decide)))

theorem fz1_28_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨3, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 3 (by decide)))

theorem fz1_28_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨4, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 4 (by decide)))

theorem fz1_28_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨5, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 5 (by decide)))

theorem fz1_28_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨6, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 6 (by decide)))

theorem fz1_28_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨7, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 7 (by decide)))

theorem fz1_28_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨8, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 8 (by decide)))

theorem fz1_28_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨9, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 9 (by decide)))

theorem fz1_28_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨10, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 10 (by decide)))

theorem fz1_28_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨11, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 11 (by decide)))

theorem fz1_28_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨13, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 13 (by decide)))

theorem fz1_28_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨14, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 14 (by decide)))

theorem fz1_28_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨15, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 15 (by decide)))

theorem fz1_28_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨16, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 16 (by decide)))

theorem fz1_28_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨17, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 17 (by decide)))

theorem fz1_28_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨18, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 18 (by decide)))

theorem fz1_28_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨19, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 19 (by decide)))

theorem fz1_28_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨20, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 20 (by decide)))

theorem fz1_28_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨21, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 21 (by decide)))

theorem fz1_28_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨22, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 22 (by decide)))

theorem fz1_28_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨23, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 23 (by decide)))

theorem fz1_28_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨24, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 24 (by decide)))

theorem fz1_28_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨25, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 25 (by decide)))

theorem fz1_28_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨26, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 26 (by decide)))

theorem fz1_28_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨27, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 27 (by decide)))

theorem fz1_28_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨29, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 29 (by decide)))

theorem fz1_28_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨30, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 30 (by decide)))

theorem fz1_28_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨31, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 31 (by decide)))

theorem fz1_28_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨32, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 32 (by decide)))

theorem fz1_28_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨33, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 33 (by decide)))

theorem fz1_28_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨34, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 34 (by decide)))

theorem fz1_28_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨35, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 35 (by decide)))

theorem fz1_28_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨36, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 36 (by decide)))

theorem fz1_28_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨37, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 37 (by decide)))

theorem fz1_28_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨38, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 38 (by decide)))

theorem fz1_28_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨39, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 39 (by decide)))

theorem fz1_28_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨40, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 40 (by decide)))

theorem fz1_28_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨41, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 41 (by decide)))

theorem fz1_28_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨42, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 42 (by decide)))

theorem fz1_28_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨43, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 43 (by decide)))

theorem fz1_28_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨44, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 44 (by decide)))

theorem fz1_28_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨45, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 45 (by decide)))

theorem fz1_28_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨46, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 46 (by decide)))

theorem fz1_28_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨47, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 47 (by decide)))

theorem fz1_28_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨48, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 48 (by decide)))

theorem fz1_28_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨49, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 49 (by decide)))

theorem fz1_28_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨50, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 50 (by decide)))

theorem fz1_28_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨51, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 51 (by decide)))

theorem fz1_28_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨52, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 52 (by decide)))

theorem fz1_28_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨53, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 53 (by decide)))

theorem fz1_28_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK28)) = 0 :=
  repsFixedCard rK28 ⟨54, by decide⟩ R28 hpxR28 hcardq28
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_28) 54 (by decide)))

theorem fixz2_28 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK28) (retConj 2 (Q2.R28_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_28_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨1, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 1 (by decide)))

theorem fz2_28_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨2, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 2 (by decide)))

theorem fz2_28_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨3, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 3 (by decide)))

theorem fz2_28_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨4, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 4 (by decide)))

theorem fz2_28_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨5, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 5 (by decide)))

theorem fz2_28_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨6, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 6 (by decide)))

theorem fz2_28_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨7, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 7 (by decide)))

theorem fz2_28_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨8, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 8 (by decide)))

theorem fz2_28_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨9, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 9 (by decide)))

theorem fz2_28_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨10, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 10 (by decide)))

theorem fz2_28_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨11, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 11 (by decide)))

theorem fz2_28_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨13, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 13 (by decide)))

theorem fz2_28_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨14, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 14 (by decide)))

theorem fz2_28_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨15, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 15 (by decide)))

theorem fz2_28_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨16, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 16 (by decide)))

theorem fz2_28_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨17, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 17 (by decide)))

theorem fz2_28_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨18, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 18 (by decide)))

theorem fz2_28_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨19, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 19 (by decide)))

theorem fz2_28_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨20, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 20 (by decide)))

theorem fz2_28_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨21, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 21 (by decide)))

theorem fz2_28_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨22, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 22 (by decide)))

theorem fz2_28_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨23, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 23 (by decide)))

theorem fz2_28_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨24, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 24 (by decide)))

theorem fz2_28_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨25, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 25 (by decide)))

theorem fz2_28_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨26, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 26 (by decide)))

theorem fz2_28_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨27, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 27 (by decide)))

theorem fz2_28_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨29, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 29 (by decide)))

theorem fz2_28_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨30, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 30 (by decide)))

theorem fz2_28_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨31, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 31 (by decide)))

theorem fz2_28_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨32, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 32 (by decide)))

theorem fz2_28_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨33, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 33 (by decide)))

theorem fz2_28_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨34, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 34 (by decide)))

theorem fz2_28_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨35, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 35 (by decide)))

theorem fz2_28_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨36, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 36 (by decide)))

theorem fz2_28_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨37, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 37 (by decide)))

theorem fz2_28_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨38, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 38 (by decide)))

theorem fz2_28_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨39, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 39 (by decide)))

theorem fz2_28_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨40, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 40 (by decide)))

theorem fz2_28_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨41, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 41 (by decide)))

theorem fz2_28_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨42, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 42 (by decide)))

theorem fz2_28_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨43, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 43 (by decide)))

theorem fz2_28_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨44, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 44 (by decide)))

theorem fz2_28_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨45, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 45 (by decide)))

theorem fz2_28_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨46, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 46 (by decide)))

theorem fz2_28_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨47, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 47 (by decide)))

theorem fz2_28_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨48, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 48 (by decide)))

theorem fz2_28_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨49, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 49 (by decide)))

theorem fz2_28_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨50, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 50 (by decide)))

theorem fz2_28_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨51, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 51 (by decide)))

theorem fz2_28_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨52, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 52 (by decide)))

theorem fz2_28_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨53, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 53 (by decide)))

theorem fz2_28_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK28)) = 0 :=
  Q2.repsFixedCard2 rK28 ⟨54, by decide⟩ Q2.R28_2 Q2.hpxR28_2 Q2.hcardq28_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_28) 54 (by decide)))

end LeanDring.P5Presentation
