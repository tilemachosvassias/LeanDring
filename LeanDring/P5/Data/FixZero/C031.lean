/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C019

/-!
# Species-table cells, off-support emptiness certificates, chunk 30

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

theorem fixz1_31 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK31) (retConj 1 (R31 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_31_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨1, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 1 (by decide)))

theorem fz1_31_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨2, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 2 (by decide)))

theorem fz1_31_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨3, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 3 (by decide)))

theorem fz1_31_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨4, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 4 (by decide)))

theorem fz1_31_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨5, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 5 (by decide)))

theorem fz1_31_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨6, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 6 (by decide)))

theorem fz1_31_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨7, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 7 (by decide)))

theorem fz1_31_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨8, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 8 (by decide)))

theorem fz1_31_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨9, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 9 (by decide)))

theorem fz1_31_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨10, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 10 (by decide)))

theorem fz1_31_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨11, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 11 (by decide)))

theorem fz1_31_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨13, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 13 (by decide)))

theorem fz1_31_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨14, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 14 (by decide)))

theorem fz1_31_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨15, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 15 (by decide)))

theorem fz1_31_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨16, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 16 (by decide)))

theorem fz1_31_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨17, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 17 (by decide)))

theorem fz1_31_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨18, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 18 (by decide)))

theorem fz1_31_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨19, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 19 (by decide)))

theorem fz1_31_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨20, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 20 (by decide)))

theorem fz1_31_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨21, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 21 (by decide)))

theorem fz1_31_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨22, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 22 (by decide)))

theorem fz1_31_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨23, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 23 (by decide)))

theorem fz1_31_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨24, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 24 (by decide)))

theorem fz1_31_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨25, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 25 (by decide)))

theorem fz1_31_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨26, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 26 (by decide)))

theorem fz1_31_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨27, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 27 (by decide)))

theorem fz1_31_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨28, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 28 (by decide)))

theorem fz1_31_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨29, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 29 (by decide)))

theorem fz1_31_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨30, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 30 (by decide)))

theorem fz1_31_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨32, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 32 (by decide)))

theorem fz1_31_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨33, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 33 (by decide)))

theorem fz1_31_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨34, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 34 (by decide)))

theorem fz1_31_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨35, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 35 (by decide)))

theorem fz1_31_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨36, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 36 (by decide)))

theorem fz1_31_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨37, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 37 (by decide)))

theorem fz1_31_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨38, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 38 (by decide)))

theorem fz1_31_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨39, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 39 (by decide)))

theorem fz1_31_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨40, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 40 (by decide)))

theorem fz1_31_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨41, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 41 (by decide)))

theorem fz1_31_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨42, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 42 (by decide)))

theorem fz1_31_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨43, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 43 (by decide)))

theorem fz1_31_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨44, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 44 (by decide)))

theorem fz1_31_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨45, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 45 (by decide)))

theorem fz1_31_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨46, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 46 (by decide)))

theorem fz1_31_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨47, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 47 (by decide)))

theorem fz1_31_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨48, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 48 (by decide)))

theorem fz1_31_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨49, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 49 (by decide)))

theorem fz1_31_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨50, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 50 (by decide)))

theorem fz1_31_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨51, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 51 (by decide)))

theorem fz1_31_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨52, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 52 (by decide)))

theorem fz1_31_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨53, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 53 (by decide)))

theorem fz1_31_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK31)) = 0 :=
  repsFixedCard rK31 ⟨54, by decide⟩ R31 hpxR31 hcardq31
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_31) 54 (by decide)))

theorem fixz2_31 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK31) (retConj 2 (Q2.R31_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_31_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨1, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 1 (by decide)))

theorem fz2_31_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨2, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 2 (by decide)))

theorem fz2_31_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨3, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 3 (by decide)))

theorem fz2_31_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨4, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 4 (by decide)))

theorem fz2_31_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨5, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 5 (by decide)))

theorem fz2_31_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨6, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 6 (by decide)))

theorem fz2_31_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨7, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 7 (by decide)))

theorem fz2_31_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨8, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 8 (by decide)))

theorem fz2_31_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨9, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 9 (by decide)))

theorem fz2_31_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨10, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 10 (by decide)))

theorem fz2_31_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨11, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 11 (by decide)))

theorem fz2_31_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨13, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 13 (by decide)))

theorem fz2_31_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨14, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 14 (by decide)))

theorem fz2_31_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨15, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 15 (by decide)))

theorem fz2_31_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨16, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 16 (by decide)))

theorem fz2_31_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨17, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 17 (by decide)))

theorem fz2_31_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨18, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 18 (by decide)))

theorem fz2_31_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨19, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 19 (by decide)))

theorem fz2_31_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨20, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 20 (by decide)))

theorem fz2_31_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨21, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 21 (by decide)))

theorem fz2_31_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨22, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 22 (by decide)))

theorem fz2_31_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨23, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 23 (by decide)))

theorem fz2_31_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨24, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 24 (by decide)))

theorem fz2_31_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨25, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 25 (by decide)))

theorem fz2_31_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨26, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 26 (by decide)))

theorem fz2_31_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨27, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 27 (by decide)))

theorem fz2_31_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨28, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 28 (by decide)))

theorem fz2_31_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨29, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 29 (by decide)))

theorem fz2_31_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨30, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 30 (by decide)))

theorem fz2_31_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨32, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 32 (by decide)))

theorem fz2_31_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨33, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 33 (by decide)))

theorem fz2_31_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨34, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 34 (by decide)))

theorem fz2_31_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨35, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 35 (by decide)))

theorem fz2_31_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨36, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 36 (by decide)))

theorem fz2_31_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨37, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 37 (by decide)))

theorem fz2_31_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨38, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 38 (by decide)))

theorem fz2_31_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨39, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 39 (by decide)))

theorem fz2_31_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨40, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 40 (by decide)))

theorem fz2_31_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨41, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 41 (by decide)))

theorem fz2_31_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨42, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 42 (by decide)))

theorem fz2_31_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨43, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 43 (by decide)))

theorem fz2_31_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨44, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 44 (by decide)))

theorem fz2_31_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨45, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 45 (by decide)))

theorem fz2_31_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨46, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 46 (by decide)))

theorem fz2_31_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨47, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 47 (by decide)))

theorem fz2_31_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨48, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 48 (by decide)))

theorem fz2_31_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨49, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 49 (by decide)))

theorem fz2_31_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨50, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 50 (by decide)))

theorem fz2_31_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨51, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 51 (by decide)))

theorem fz2_31_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨52, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 52 (by decide)))

theorem fz2_31_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨53, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 53 (by decide)))

theorem fz2_31_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK31)) = 0 :=
  Q2.repsFixedCard2 rK31 ⟨54, by decide⟩ Q2.R31_2 Q2.hpxR31_2 Q2.hcardq31_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_31) 54 (by decide)))

end LeanDring.P5Presentation
