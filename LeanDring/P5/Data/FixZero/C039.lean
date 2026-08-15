/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C027

/-!
# Species-table cells, off-support emptiness certificates, chunk 38

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

theorem fixz1_39 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK39) (retConj 1 (R39 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_39_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨1, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 1 (by decide)))

theorem fz1_39_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨2, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 2 (by decide)))

theorem fz1_39_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨3, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 3 (by decide)))

theorem fz1_39_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨4, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 4 (by decide)))

theorem fz1_39_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨5, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 5 (by decide)))

theorem fz1_39_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨6, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 6 (by decide)))

theorem fz1_39_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨7, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 7 (by decide)))

theorem fz1_39_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨8, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 8 (by decide)))

theorem fz1_39_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨9, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 9 (by decide)))

theorem fz1_39_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨10, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 10 (by decide)))

theorem fz1_39_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨11, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 11 (by decide)))

theorem fz1_39_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨13, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 13 (by decide)))

theorem fz1_39_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨14, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 14 (by decide)))

theorem fz1_39_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨15, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 15 (by decide)))

theorem fz1_39_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨16, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 16 (by decide)))

theorem fz1_39_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨17, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 17 (by decide)))

theorem fz1_39_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨18, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 18 (by decide)))

theorem fz1_39_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨19, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 19 (by decide)))

theorem fz1_39_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨20, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 20 (by decide)))

theorem fz1_39_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨21, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 21 (by decide)))

theorem fz1_39_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨22, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 22 (by decide)))

theorem fz1_39_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨23, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 23 (by decide)))

theorem fz1_39_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨24, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 24 (by decide)))

theorem fz1_39_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨25, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 25 (by decide)))

theorem fz1_39_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨26, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 26 (by decide)))

theorem fz1_39_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨27, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 27 (by decide)))

theorem fz1_39_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨28, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 28 (by decide)))

theorem fz1_39_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨29, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 29 (by decide)))

theorem fz1_39_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨30, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 30 (by decide)))

theorem fz1_39_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨31, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 31 (by decide)))

theorem fz1_39_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨32, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 32 (by decide)))

theorem fz1_39_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨33, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 33 (by decide)))

theorem fz1_39_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨34, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 34 (by decide)))

theorem fz1_39_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨35, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 35 (by decide)))

theorem fz1_39_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨36, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 36 (by decide)))

theorem fz1_39_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨37, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 37 (by decide)))

theorem fz1_39_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨38, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 38 (by decide)))

theorem fz1_39_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨40, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 40 (by decide)))

theorem fz1_39_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨41, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 41 (by decide)))

theorem fz1_39_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨42, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 42 (by decide)))

theorem fz1_39_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨43, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 43 (by decide)))

theorem fz1_39_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨44, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 44 (by decide)))

theorem fz1_39_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨45, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 45 (by decide)))

theorem fz1_39_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨46, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 46 (by decide)))

theorem fz1_39_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨47, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 47 (by decide)))

theorem fz1_39_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨48, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 48 (by decide)))

theorem fz1_39_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨49, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 49 (by decide)))

theorem fz1_39_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨50, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 50 (by decide)))

theorem fz1_39_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨51, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 51 (by decide)))

theorem fz1_39_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨52, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 52 (by decide)))

theorem fz1_39_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨53, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 53 (by decide)))

theorem fz1_39_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK39)) = 0 :=
  repsFixedCard rK39 ⟨54, by decide⟩ R39 hpxR39 hcardq39
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_39) 54 (by decide)))

theorem fixz2_39 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK39) (retConj 2 (Q2.R39_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_39_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨1, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 1 (by decide)))

theorem fz2_39_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨2, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 2 (by decide)))

theorem fz2_39_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨3, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 3 (by decide)))

theorem fz2_39_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨4, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 4 (by decide)))

theorem fz2_39_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨5, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 5 (by decide)))

theorem fz2_39_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨6, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 6 (by decide)))

theorem fz2_39_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨7, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 7 (by decide)))

theorem fz2_39_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨8, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 8 (by decide)))

theorem fz2_39_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨9, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 9 (by decide)))

theorem fz2_39_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨10, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 10 (by decide)))

theorem fz2_39_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨11, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 11 (by decide)))

theorem fz2_39_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨13, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 13 (by decide)))

theorem fz2_39_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨14, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 14 (by decide)))

theorem fz2_39_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨15, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 15 (by decide)))

theorem fz2_39_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨16, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 16 (by decide)))

theorem fz2_39_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨17, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 17 (by decide)))

theorem fz2_39_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨18, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 18 (by decide)))

theorem fz2_39_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨19, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 19 (by decide)))

theorem fz2_39_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨20, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 20 (by decide)))

theorem fz2_39_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨21, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 21 (by decide)))

theorem fz2_39_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨22, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 22 (by decide)))

theorem fz2_39_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨23, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 23 (by decide)))

theorem fz2_39_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨24, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 24 (by decide)))

theorem fz2_39_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨25, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 25 (by decide)))

theorem fz2_39_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨26, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 26 (by decide)))

theorem fz2_39_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨27, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 27 (by decide)))

theorem fz2_39_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨28, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 28 (by decide)))

theorem fz2_39_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨29, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 29 (by decide)))

theorem fz2_39_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨30, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 30 (by decide)))

theorem fz2_39_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨31, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 31 (by decide)))

theorem fz2_39_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨32, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 32 (by decide)))

theorem fz2_39_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨33, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 33 (by decide)))

theorem fz2_39_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨34, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 34 (by decide)))

theorem fz2_39_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨35, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 35 (by decide)))

theorem fz2_39_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨36, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 36 (by decide)))

theorem fz2_39_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨37, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 37 (by decide)))

theorem fz2_39_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨38, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 38 (by decide)))

theorem fz2_39_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨40, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 40 (by decide)))

theorem fz2_39_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨41, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 41 (by decide)))

theorem fz2_39_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨42, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 42 (by decide)))

theorem fz2_39_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨43, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 43 (by decide)))

theorem fz2_39_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨44, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 44 (by decide)))

theorem fz2_39_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨45, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 45 (by decide)))

theorem fz2_39_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨46, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 46 (by decide)))

theorem fz2_39_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨47, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 47 (by decide)))

theorem fz2_39_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨48, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 48 (by decide)))

theorem fz2_39_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨49, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 49 (by decide)))

theorem fz2_39_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨50, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 50 (by decide)))

theorem fz2_39_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨51, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 51 (by decide)))

theorem fz2_39_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨52, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 52 (by decide)))

theorem fz2_39_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨53, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 53 (by decide)))

theorem fz2_39_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK39)) = 0 :=
  Q2.repsFixedCard2 rK39 ⟨54, by decide⟩ Q2.R39_2 Q2.hpxR39_2 Q2.hcardq39_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_39) 54 (by decide)))

end LeanDring.P5Presentation
