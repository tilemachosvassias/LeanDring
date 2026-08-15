/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C017

/-!
# Species-table cells, off-support emptiness certificates, chunk 28

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

theorem fixz1_29 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK29) (retConj 1 (R29 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_29_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨1, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 1 (by decide)))

theorem fz1_29_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨2, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 2 (by decide)))

theorem fz1_29_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨3, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 3 (by decide)))

theorem fz1_29_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨4, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 4 (by decide)))

theorem fz1_29_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨5, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 5 (by decide)))

theorem fz1_29_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨6, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 6 (by decide)))

theorem fz1_29_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨7, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 7 (by decide)))

theorem fz1_29_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨8, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 8 (by decide)))

theorem fz1_29_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨9, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 9 (by decide)))

theorem fz1_29_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨10, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 10 (by decide)))

theorem fz1_29_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨11, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 11 (by decide)))

theorem fz1_29_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨13, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 13 (by decide)))

theorem fz1_29_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨14, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 14 (by decide)))

theorem fz1_29_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨15, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 15 (by decide)))

theorem fz1_29_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨16, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 16 (by decide)))

theorem fz1_29_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨17, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 17 (by decide)))

theorem fz1_29_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨18, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 18 (by decide)))

theorem fz1_29_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨19, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 19 (by decide)))

theorem fz1_29_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨20, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 20 (by decide)))

theorem fz1_29_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨21, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 21 (by decide)))

theorem fz1_29_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨22, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 22 (by decide)))

theorem fz1_29_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨23, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 23 (by decide)))

theorem fz1_29_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨24, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 24 (by decide)))

theorem fz1_29_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨25, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 25 (by decide)))

theorem fz1_29_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨26, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 26 (by decide)))

theorem fz1_29_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨27, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 27 (by decide)))

theorem fz1_29_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨28, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 28 (by decide)))

theorem fz1_29_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨30, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 30 (by decide)))

theorem fz1_29_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨31, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 31 (by decide)))

theorem fz1_29_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨32, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 32 (by decide)))

theorem fz1_29_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨33, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 33 (by decide)))

theorem fz1_29_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨34, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 34 (by decide)))

theorem fz1_29_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨35, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 35 (by decide)))

theorem fz1_29_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨36, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 36 (by decide)))

theorem fz1_29_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨37, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 37 (by decide)))

theorem fz1_29_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨38, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 38 (by decide)))

theorem fz1_29_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨39, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 39 (by decide)))

theorem fz1_29_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨40, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 40 (by decide)))

theorem fz1_29_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨41, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 41 (by decide)))

theorem fz1_29_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨42, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 42 (by decide)))

theorem fz1_29_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨43, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 43 (by decide)))

theorem fz1_29_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨44, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 44 (by decide)))

theorem fz1_29_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨45, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 45 (by decide)))

theorem fz1_29_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨46, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 46 (by decide)))

theorem fz1_29_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨47, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 47 (by decide)))

theorem fz1_29_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨48, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 48 (by decide)))

theorem fz1_29_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨49, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 49 (by decide)))

theorem fz1_29_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨50, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 50 (by decide)))

theorem fz1_29_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨51, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 51 (by decide)))

theorem fz1_29_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨52, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 52 (by decide)))

theorem fz1_29_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨53, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 53 (by decide)))

theorem fz1_29_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK29)) = 0 :=
  repsFixedCard rK29 ⟨54, by decide⟩ R29 hpxR29 hcardq29
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_29) 54 (by decide)))

theorem fixz2_29 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK29) (retConj 2 (Q2.R29_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_29_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨1, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 1 (by decide)))

theorem fz2_29_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨2, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 2 (by decide)))

theorem fz2_29_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨3, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 3 (by decide)))

theorem fz2_29_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨4, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 4 (by decide)))

theorem fz2_29_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨5, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 5 (by decide)))

theorem fz2_29_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨6, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 6 (by decide)))

theorem fz2_29_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨7, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 7 (by decide)))

theorem fz2_29_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨8, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 8 (by decide)))

theorem fz2_29_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨9, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 9 (by decide)))

theorem fz2_29_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨10, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 10 (by decide)))

theorem fz2_29_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨11, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 11 (by decide)))

theorem fz2_29_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨13, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 13 (by decide)))

theorem fz2_29_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨14, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 14 (by decide)))

theorem fz2_29_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨15, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 15 (by decide)))

theorem fz2_29_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨16, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 16 (by decide)))

theorem fz2_29_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨17, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 17 (by decide)))

theorem fz2_29_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨18, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 18 (by decide)))

theorem fz2_29_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨19, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 19 (by decide)))

theorem fz2_29_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨20, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 20 (by decide)))

theorem fz2_29_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨21, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 21 (by decide)))

theorem fz2_29_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨22, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 22 (by decide)))

theorem fz2_29_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨23, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 23 (by decide)))

theorem fz2_29_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨24, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 24 (by decide)))

theorem fz2_29_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨25, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 25 (by decide)))

theorem fz2_29_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨26, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 26 (by decide)))

theorem fz2_29_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨27, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 27 (by decide)))

theorem fz2_29_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨28, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 28 (by decide)))

theorem fz2_29_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨30, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 30 (by decide)))

theorem fz2_29_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨31, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 31 (by decide)))

theorem fz2_29_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨32, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 32 (by decide)))

theorem fz2_29_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨33, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 33 (by decide)))

theorem fz2_29_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨34, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 34 (by decide)))

theorem fz2_29_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨35, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 35 (by decide)))

theorem fz2_29_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨36, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 36 (by decide)))

theorem fz2_29_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨37, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 37 (by decide)))

theorem fz2_29_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨38, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 38 (by decide)))

theorem fz2_29_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨39, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 39 (by decide)))

theorem fz2_29_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨40, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 40 (by decide)))

theorem fz2_29_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨41, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 41 (by decide)))

theorem fz2_29_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨42, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 42 (by decide)))

theorem fz2_29_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨43, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 43 (by decide)))

theorem fz2_29_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨44, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 44 (by decide)))

theorem fz2_29_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨45, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 45 (by decide)))

theorem fz2_29_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨46, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 46 (by decide)))

theorem fz2_29_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨47, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 47 (by decide)))

theorem fz2_29_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨48, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 48 (by decide)))

theorem fz2_29_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨49, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 49 (by decide)))

theorem fz2_29_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨50, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 50 (by decide)))

theorem fz2_29_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨51, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 51 (by decide)))

theorem fz2_29_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨52, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 52 (by decide)))

theorem fz2_29_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨53, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 53 (by decide)))

theorem fz2_29_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK29)) = 0 :=
  Q2.repsFixedCard2 rK29 ⟨54, by decide⟩ Q2.R29_2 Q2.hpxR29_2 Q2.hcardq29_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_29) 54 (by decide)))

end LeanDring.P5Presentation
