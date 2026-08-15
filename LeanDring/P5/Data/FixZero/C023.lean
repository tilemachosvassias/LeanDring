/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C011

/-!
# Species-table cells, off-support emptiness certificates, chunk 22

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

theorem fixz1_23 : ([1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK23) (retConj 1 (R23 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_23_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨1, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 1 (by decide)))

theorem fz1_23_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨2, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 2 (by decide)))

theorem fz1_23_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨3, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 3 (by decide)))

theorem fz1_23_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨4, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 4 (by decide)))

theorem fz1_23_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨6, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 6 (by decide)))

theorem fz1_23_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨7, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 7 (by decide)))

theorem fz1_23_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨8, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 8 (by decide)))

theorem fz1_23_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨9, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 9 (by decide)))

theorem fz1_23_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨10, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 10 (by decide)))

theorem fz1_23_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨11, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 11 (by decide)))

theorem fz1_23_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨13, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 13 (by decide)))

theorem fz1_23_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨14, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 14 (by decide)))

theorem fz1_23_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨15, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 15 (by decide)))

theorem fz1_23_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨16, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 16 (by decide)))

theorem fz1_23_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨17, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 17 (by decide)))

theorem fz1_23_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨18, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 18 (by decide)))

theorem fz1_23_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨19, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 19 (by decide)))

theorem fz1_23_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨20, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 20 (by decide)))

theorem fz1_23_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨21, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 21 (by decide)))

theorem fz1_23_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨22, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 22 (by decide)))

theorem fz1_23_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨24, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 24 (by decide)))

theorem fz1_23_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨25, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 25 (by decide)))

theorem fz1_23_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨26, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 26 (by decide)))

theorem fz1_23_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨27, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 27 (by decide)))

theorem fz1_23_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨28, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 28 (by decide)))

theorem fz1_23_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨29, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 29 (by decide)))

theorem fz1_23_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨30, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 30 (by decide)))

theorem fz1_23_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨31, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 31 (by decide)))

theorem fz1_23_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨32, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 32 (by decide)))

theorem fz1_23_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨33, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 33 (by decide)))

theorem fz1_23_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨34, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 34 (by decide)))

theorem fz1_23_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨35, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 35 (by decide)))

theorem fz1_23_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨36, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 36 (by decide)))

theorem fz1_23_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨37, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 37 (by decide)))

theorem fz1_23_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨38, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 38 (by decide)))

theorem fz1_23_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨39, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 39 (by decide)))

theorem fz1_23_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨40, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 40 (by decide)))

theorem fz1_23_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨41, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 41 (by decide)))

theorem fz1_23_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨42, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 42 (by decide)))

theorem fz1_23_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨43, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 43 (by decide)))

theorem fz1_23_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨44, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 44 (by decide)))

theorem fz1_23_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨45, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 45 (by decide)))

theorem fz1_23_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨46, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 46 (by decide)))

theorem fz1_23_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨47, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 47 (by decide)))

theorem fz1_23_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨48, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 48 (by decide)))

theorem fz1_23_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨49, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 49 (by decide)))

theorem fz1_23_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨50, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 50 (by decide)))

theorem fz1_23_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨51, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 51 (by decide)))

theorem fz1_23_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨52, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 52 (by decide)))

theorem fz1_23_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨53, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 53 (by decide)))

theorem fz1_23_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK23)) = 0 :=
  repsFixedCard rK23 ⟨54, by decide⟩ R23 hpxR23 hcardq23
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_23) 54 (by decide)))

theorem fixz2_23 : ([1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK23) (retConj 2 (Q2.R23_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_23_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨1, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 1 (by decide)))

theorem fz2_23_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨2, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 2 (by decide)))

theorem fz2_23_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨3, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 3 (by decide)))

theorem fz2_23_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨4, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 4 (by decide)))

theorem fz2_23_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨6, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 6 (by decide)))

theorem fz2_23_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨7, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 7 (by decide)))

theorem fz2_23_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨8, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 8 (by decide)))

theorem fz2_23_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨9, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 9 (by decide)))

theorem fz2_23_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨10, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 10 (by decide)))

theorem fz2_23_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨11, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 11 (by decide)))

theorem fz2_23_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨13, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 13 (by decide)))

theorem fz2_23_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨14, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 14 (by decide)))

theorem fz2_23_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨15, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 15 (by decide)))

theorem fz2_23_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨16, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 16 (by decide)))

theorem fz2_23_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨17, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 17 (by decide)))

theorem fz2_23_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨18, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 18 (by decide)))

theorem fz2_23_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨19, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 19 (by decide)))

theorem fz2_23_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨20, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 20 (by decide)))

theorem fz2_23_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨21, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 21 (by decide)))

theorem fz2_23_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨22, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 22 (by decide)))

theorem fz2_23_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨24, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 24 (by decide)))

theorem fz2_23_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨25, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 25 (by decide)))

theorem fz2_23_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨26, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 26 (by decide)))

theorem fz2_23_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨27, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 27 (by decide)))

theorem fz2_23_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨28, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 28 (by decide)))

theorem fz2_23_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨29, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 29 (by decide)))

theorem fz2_23_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨30, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 30 (by decide)))

theorem fz2_23_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨31, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 31 (by decide)))

theorem fz2_23_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨32, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 32 (by decide)))

theorem fz2_23_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨33, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 33 (by decide)))

theorem fz2_23_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨34, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 34 (by decide)))

theorem fz2_23_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨35, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 35 (by decide)))

theorem fz2_23_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨36, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 36 (by decide)))

theorem fz2_23_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨37, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 37 (by decide)))

theorem fz2_23_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨38, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 38 (by decide)))

theorem fz2_23_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨39, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 39 (by decide)))

theorem fz2_23_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨40, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 40 (by decide)))

theorem fz2_23_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨41, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 41 (by decide)))

theorem fz2_23_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨42, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 42 (by decide)))

theorem fz2_23_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨43, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 43 (by decide)))

theorem fz2_23_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨44, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 44 (by decide)))

theorem fz2_23_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨45, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 45 (by decide)))

theorem fz2_23_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨46, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 46 (by decide)))

theorem fz2_23_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨47, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 47 (by decide)))

theorem fz2_23_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨48, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 48 (by decide)))

theorem fz2_23_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨49, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 49 (by decide)))

theorem fz2_23_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨50, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 50 (by decide)))

theorem fz2_23_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨51, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 51 (by decide)))

theorem fz2_23_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨52, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 52 (by decide)))

theorem fz2_23_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨53, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 53 (by decide)))

theorem fz2_23_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK23)) = 0 :=
  Q2.repsFixedCard2 rK23 ⟨54, by decide⟩ Q2.R23_2 Q2.hpxR23_2 Q2.hcardq23_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_23) 54 (by decide)))

end LeanDring.P5Presentation
