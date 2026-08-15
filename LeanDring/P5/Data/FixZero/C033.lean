/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C021

/-!
# Species-table cells, off-support emptiness certificates, chunk 32

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

theorem fixz1_33 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK33) (retConj 1 (R33 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_33_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨1, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 1 (by decide)))

theorem fz1_33_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨2, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 2 (by decide)))

theorem fz1_33_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨3, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 3 (by decide)))

theorem fz1_33_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨4, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 4 (by decide)))

theorem fz1_33_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨5, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 5 (by decide)))

theorem fz1_33_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨6, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 6 (by decide)))

theorem fz1_33_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨7, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 7 (by decide)))

theorem fz1_33_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨8, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 8 (by decide)))

theorem fz1_33_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨9, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 9 (by decide)))

theorem fz1_33_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨10, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 10 (by decide)))

theorem fz1_33_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨11, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 11 (by decide)))

theorem fz1_33_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨13, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 13 (by decide)))

theorem fz1_33_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨14, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 14 (by decide)))

theorem fz1_33_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨15, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 15 (by decide)))

theorem fz1_33_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨16, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 16 (by decide)))

theorem fz1_33_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨17, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 17 (by decide)))

theorem fz1_33_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨18, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 18 (by decide)))

theorem fz1_33_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨19, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 19 (by decide)))

theorem fz1_33_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨20, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 20 (by decide)))

theorem fz1_33_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨21, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 21 (by decide)))

theorem fz1_33_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨22, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 22 (by decide)))

theorem fz1_33_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨23, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 23 (by decide)))

theorem fz1_33_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨24, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 24 (by decide)))

theorem fz1_33_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨25, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 25 (by decide)))

theorem fz1_33_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨26, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 26 (by decide)))

theorem fz1_33_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨27, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 27 (by decide)))

theorem fz1_33_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨28, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 28 (by decide)))

theorem fz1_33_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨29, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 29 (by decide)))

theorem fz1_33_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨30, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 30 (by decide)))

theorem fz1_33_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨31, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 31 (by decide)))

theorem fz1_33_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨32, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 32 (by decide)))

theorem fz1_33_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨34, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 34 (by decide)))

theorem fz1_33_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨35, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 35 (by decide)))

theorem fz1_33_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨36, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 36 (by decide)))

theorem fz1_33_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨37, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 37 (by decide)))

theorem fz1_33_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨38, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 38 (by decide)))

theorem fz1_33_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨39, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 39 (by decide)))

theorem fz1_33_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨40, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 40 (by decide)))

theorem fz1_33_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨41, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 41 (by decide)))

theorem fz1_33_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨42, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 42 (by decide)))

theorem fz1_33_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨43, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 43 (by decide)))

theorem fz1_33_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨44, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 44 (by decide)))

theorem fz1_33_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨45, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 45 (by decide)))

theorem fz1_33_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨46, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 46 (by decide)))

theorem fz1_33_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨47, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 47 (by decide)))

theorem fz1_33_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨48, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 48 (by decide)))

theorem fz1_33_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨49, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 49 (by decide)))

theorem fz1_33_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨50, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 50 (by decide)))

theorem fz1_33_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨51, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 51 (by decide)))

theorem fz1_33_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨52, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 52 (by decide)))

theorem fz1_33_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨53, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 53 (by decide)))

theorem fz1_33_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK33)) = 0 :=
  repsFixedCard rK33 ⟨54, by decide⟩ R33 hpxR33 hcardq33
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_33) 54 (by decide)))

theorem fixz2_33 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK33) (retConj 2 (Q2.R33_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_33_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨1, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 1 (by decide)))

theorem fz2_33_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨2, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 2 (by decide)))

theorem fz2_33_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨3, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 3 (by decide)))

theorem fz2_33_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨4, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 4 (by decide)))

theorem fz2_33_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨5, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 5 (by decide)))

theorem fz2_33_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨6, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 6 (by decide)))

theorem fz2_33_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨7, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 7 (by decide)))

theorem fz2_33_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨8, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 8 (by decide)))

theorem fz2_33_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨9, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 9 (by decide)))

theorem fz2_33_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨10, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 10 (by decide)))

theorem fz2_33_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨11, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 11 (by decide)))

theorem fz2_33_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨13, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 13 (by decide)))

theorem fz2_33_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨14, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 14 (by decide)))

theorem fz2_33_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨15, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 15 (by decide)))

theorem fz2_33_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨16, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 16 (by decide)))

theorem fz2_33_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨17, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 17 (by decide)))

theorem fz2_33_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨18, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 18 (by decide)))

theorem fz2_33_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨19, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 19 (by decide)))

theorem fz2_33_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨20, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 20 (by decide)))

theorem fz2_33_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨21, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 21 (by decide)))

theorem fz2_33_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨22, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 22 (by decide)))

theorem fz2_33_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨23, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 23 (by decide)))

theorem fz2_33_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨24, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 24 (by decide)))

theorem fz2_33_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨25, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 25 (by decide)))

theorem fz2_33_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨26, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 26 (by decide)))

theorem fz2_33_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨27, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 27 (by decide)))

theorem fz2_33_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨28, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 28 (by decide)))

theorem fz2_33_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨29, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 29 (by decide)))

theorem fz2_33_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨30, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 30 (by decide)))

theorem fz2_33_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨31, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 31 (by decide)))

theorem fz2_33_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨32, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 32 (by decide)))

theorem fz2_33_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨34, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 34 (by decide)))

theorem fz2_33_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨35, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 35 (by decide)))

theorem fz2_33_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨36, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 36 (by decide)))

theorem fz2_33_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨37, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 37 (by decide)))

theorem fz2_33_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨38, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 38 (by decide)))

theorem fz2_33_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨39, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 39 (by decide)))

theorem fz2_33_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨40, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 40 (by decide)))

theorem fz2_33_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨41, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 41 (by decide)))

theorem fz2_33_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨42, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 42 (by decide)))

theorem fz2_33_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨43, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 43 (by decide)))

theorem fz2_33_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨44, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 44 (by decide)))

theorem fz2_33_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨45, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 45 (by decide)))

theorem fz2_33_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨46, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 46 (by decide)))

theorem fz2_33_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨47, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 47 (by decide)))

theorem fz2_33_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨48, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 48 (by decide)))

theorem fz2_33_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨49, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 49 (by decide)))

theorem fz2_33_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨50, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 50 (by decide)))

theorem fz2_33_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨51, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 51 (by decide)))

theorem fz2_33_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨52, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 52 (by decide)))

theorem fz2_33_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨53, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 53 (by decide)))

theorem fz2_33_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK33)) = 0 :=
  Q2.repsFixedCard2 rK33 ⟨54, by decide⟩ Q2.R33_2 Q2.hpxR33_2 Q2.hcardq33_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_33) 54 (by decide)))

end LeanDring.P5Presentation
