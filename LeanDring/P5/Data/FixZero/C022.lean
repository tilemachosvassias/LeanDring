/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C010

/-!
# Species-table cells, off-support emptiness certificates, chunk 21

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

theorem fixz1_22 : ([1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK22) (retConj 1 (R22 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_22_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨1, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 1 (by decide)))

theorem fz1_22_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨2, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 2 (by decide)))

theorem fz1_22_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨3, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 3 (by decide)))

theorem fz1_22_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨5, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 5 (by decide)))

theorem fz1_22_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨6, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 6 (by decide)))

theorem fz1_22_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨7, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 7 (by decide)))

theorem fz1_22_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨8, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 8 (by decide)))

theorem fz1_22_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨9, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 9 (by decide)))

theorem fz1_22_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨10, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 10 (by decide)))

theorem fz1_22_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨11, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 11 (by decide)))

theorem fz1_22_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨13, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 13 (by decide)))

theorem fz1_22_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨14, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 14 (by decide)))

theorem fz1_22_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨15, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 15 (by decide)))

theorem fz1_22_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨16, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 16 (by decide)))

theorem fz1_22_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨17, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 17 (by decide)))

theorem fz1_22_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨18, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 18 (by decide)))

theorem fz1_22_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨19, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 19 (by decide)))

theorem fz1_22_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨20, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 20 (by decide)))

theorem fz1_22_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨21, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 21 (by decide)))

theorem fz1_22_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨23, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 23 (by decide)))

theorem fz1_22_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨24, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 24 (by decide)))

theorem fz1_22_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨25, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 25 (by decide)))

theorem fz1_22_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨26, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 26 (by decide)))

theorem fz1_22_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨27, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 27 (by decide)))

theorem fz1_22_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨28, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 28 (by decide)))

theorem fz1_22_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨29, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 29 (by decide)))

theorem fz1_22_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨30, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 30 (by decide)))

theorem fz1_22_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨31, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 31 (by decide)))

theorem fz1_22_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨32, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 32 (by decide)))

theorem fz1_22_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨33, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 33 (by decide)))

theorem fz1_22_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨34, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 34 (by decide)))

theorem fz1_22_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨35, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 35 (by decide)))

theorem fz1_22_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨36, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 36 (by decide)))

theorem fz1_22_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨37, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 37 (by decide)))

theorem fz1_22_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨38, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 38 (by decide)))

theorem fz1_22_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨39, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 39 (by decide)))

theorem fz1_22_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨40, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 40 (by decide)))

theorem fz1_22_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨41, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 41 (by decide)))

theorem fz1_22_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨42, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 42 (by decide)))

theorem fz1_22_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨43, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 43 (by decide)))

theorem fz1_22_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨44, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 44 (by decide)))

theorem fz1_22_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨45, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 45 (by decide)))

theorem fz1_22_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨46, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 46 (by decide)))

theorem fz1_22_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨47, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 47 (by decide)))

theorem fz1_22_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨48, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 48 (by decide)))

theorem fz1_22_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨49, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 49 (by decide)))

theorem fz1_22_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨50, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 50 (by decide)))

theorem fz1_22_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨51, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 51 (by decide)))

theorem fz1_22_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨52, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 52 (by decide)))

theorem fz1_22_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨53, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 53 (by decide)))

theorem fz1_22_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK22)) = 0 :=
  repsFixedCard rK22 ⟨54, by decide⟩ R22 hpxR22 hcardq22
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_22) 54 (by decide)))

theorem fixz2_22 : ([1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK22) (retConj 2 (Q2.R22_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_22_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨1, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 1 (by decide)))

theorem fz2_22_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨2, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 2 (by decide)))

theorem fz2_22_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨3, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 3 (by decide)))

theorem fz2_22_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨5, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 5 (by decide)))

theorem fz2_22_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨6, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 6 (by decide)))

theorem fz2_22_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨7, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 7 (by decide)))

theorem fz2_22_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨8, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 8 (by decide)))

theorem fz2_22_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨9, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 9 (by decide)))

theorem fz2_22_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨10, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 10 (by decide)))

theorem fz2_22_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨11, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 11 (by decide)))

theorem fz2_22_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨13, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 13 (by decide)))

theorem fz2_22_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨14, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 14 (by decide)))

theorem fz2_22_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨15, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 15 (by decide)))

theorem fz2_22_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨16, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 16 (by decide)))

theorem fz2_22_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨17, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 17 (by decide)))

theorem fz2_22_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨18, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 18 (by decide)))

theorem fz2_22_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨19, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 19 (by decide)))

theorem fz2_22_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨20, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 20 (by decide)))

theorem fz2_22_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨21, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 21 (by decide)))

theorem fz2_22_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨23, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 23 (by decide)))

theorem fz2_22_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨24, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 24 (by decide)))

theorem fz2_22_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨25, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 25 (by decide)))

theorem fz2_22_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨26, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 26 (by decide)))

theorem fz2_22_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨27, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 27 (by decide)))

theorem fz2_22_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨28, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 28 (by decide)))

theorem fz2_22_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨29, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 29 (by decide)))

theorem fz2_22_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨30, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 30 (by decide)))

theorem fz2_22_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨31, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 31 (by decide)))

theorem fz2_22_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨32, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 32 (by decide)))

theorem fz2_22_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨33, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 33 (by decide)))

theorem fz2_22_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨34, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 34 (by decide)))

theorem fz2_22_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨35, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 35 (by decide)))

theorem fz2_22_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨36, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 36 (by decide)))

theorem fz2_22_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨37, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 37 (by decide)))

theorem fz2_22_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨38, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 38 (by decide)))

theorem fz2_22_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨39, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 39 (by decide)))

theorem fz2_22_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨40, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 40 (by decide)))

theorem fz2_22_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨41, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 41 (by decide)))

theorem fz2_22_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨42, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 42 (by decide)))

theorem fz2_22_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨43, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 43 (by decide)))

theorem fz2_22_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨44, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 44 (by decide)))

theorem fz2_22_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨45, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 45 (by decide)))

theorem fz2_22_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨46, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 46 (by decide)))

theorem fz2_22_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨47, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 47 (by decide)))

theorem fz2_22_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨48, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 48 (by decide)))

theorem fz2_22_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨49, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 49 (by decide)))

theorem fz2_22_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨50, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 50 (by decide)))

theorem fz2_22_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨51, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 51 (by decide)))

theorem fz2_22_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨52, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 52 (by decide)))

theorem fz2_22_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨53, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 53 (by decide)))

theorem fz2_22_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK22)) = 0 :=
  Q2.repsFixedCard2 rK22 ⟨54, by decide⟩ Q2.R22_2 Q2.hpxR22_2 Q2.hcardq22_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_22) 54 (by decide)))

end LeanDring.P5Presentation
