/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C015

/-!
# Species-table cells, off-support emptiness certificates, chunk 26

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

theorem fixz1_27 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK27) (retConj 1 (R27 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_27_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨1, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 1 (by decide)))

theorem fz1_27_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨2, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 2 (by decide)))

theorem fz1_27_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨3, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 3 (by decide)))

theorem fz1_27_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨4, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 4 (by decide)))

theorem fz1_27_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨5, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 5 (by decide)))

theorem fz1_27_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨6, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 6 (by decide)))

theorem fz1_27_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨7, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 7 (by decide)))

theorem fz1_27_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨8, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 8 (by decide)))

theorem fz1_27_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨10, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 10 (by decide)))

theorem fz1_27_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨11, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 11 (by decide)))

theorem fz1_27_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨13, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 13 (by decide)))

theorem fz1_27_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨14, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 14 (by decide)))

theorem fz1_27_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨15, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 15 (by decide)))

theorem fz1_27_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨16, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 16 (by decide)))

theorem fz1_27_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨17, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 17 (by decide)))

theorem fz1_27_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨18, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 18 (by decide)))

theorem fz1_27_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨19, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 19 (by decide)))

theorem fz1_27_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨20, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 20 (by decide)))

theorem fz1_27_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨21, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 21 (by decide)))

theorem fz1_27_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨22, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 22 (by decide)))

theorem fz1_27_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨23, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 23 (by decide)))

theorem fz1_27_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨24, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 24 (by decide)))

theorem fz1_27_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨25, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 25 (by decide)))

theorem fz1_27_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨26, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 26 (by decide)))

theorem fz1_27_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨28, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 28 (by decide)))

theorem fz1_27_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨29, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 29 (by decide)))

theorem fz1_27_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨30, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 30 (by decide)))

theorem fz1_27_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨31, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 31 (by decide)))

theorem fz1_27_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨32, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 32 (by decide)))

theorem fz1_27_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨33, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 33 (by decide)))

theorem fz1_27_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨34, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 34 (by decide)))

theorem fz1_27_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨35, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 35 (by decide)))

theorem fz1_27_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨36, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 36 (by decide)))

theorem fz1_27_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨37, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 37 (by decide)))

theorem fz1_27_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨38, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 38 (by decide)))

theorem fz1_27_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨39, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 39 (by decide)))

theorem fz1_27_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨40, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 40 (by decide)))

theorem fz1_27_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨41, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 41 (by decide)))

theorem fz1_27_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨42, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 42 (by decide)))

theorem fz1_27_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨43, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 43 (by decide)))

theorem fz1_27_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨44, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 44 (by decide)))

theorem fz1_27_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨45, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 45 (by decide)))

theorem fz1_27_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨46, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 46 (by decide)))

theorem fz1_27_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨47, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 47 (by decide)))

theorem fz1_27_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨48, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 48 (by decide)))

theorem fz1_27_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨49, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 49 (by decide)))

theorem fz1_27_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨50, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 50 (by decide)))

theorem fz1_27_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨51, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 51 (by decide)))

theorem fz1_27_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨52, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 52 (by decide)))

theorem fz1_27_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨53, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 53 (by decide)))

theorem fz1_27_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK27)) = 0 :=
  repsFixedCard rK27 ⟨54, by decide⟩ R27 hpxR27 hcardq27
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_27) 54 (by decide)))

theorem fixz2_27 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK27) (retConj 2 (Q2.R27_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_27_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨1, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 1 (by decide)))

theorem fz2_27_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨2, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 2 (by decide)))

theorem fz2_27_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨3, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 3 (by decide)))

theorem fz2_27_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨4, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 4 (by decide)))

theorem fz2_27_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨5, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 5 (by decide)))

theorem fz2_27_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨6, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 6 (by decide)))

theorem fz2_27_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨7, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 7 (by decide)))

theorem fz2_27_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨8, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 8 (by decide)))

theorem fz2_27_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨10, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 10 (by decide)))

theorem fz2_27_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨11, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 11 (by decide)))

theorem fz2_27_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨13, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 13 (by decide)))

theorem fz2_27_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨14, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 14 (by decide)))

theorem fz2_27_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨15, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 15 (by decide)))

theorem fz2_27_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨16, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 16 (by decide)))

theorem fz2_27_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨17, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 17 (by decide)))

theorem fz2_27_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨18, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 18 (by decide)))

theorem fz2_27_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨19, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 19 (by decide)))

theorem fz2_27_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨20, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 20 (by decide)))

theorem fz2_27_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨21, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 21 (by decide)))

theorem fz2_27_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨22, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 22 (by decide)))

theorem fz2_27_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨23, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 23 (by decide)))

theorem fz2_27_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨24, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 24 (by decide)))

theorem fz2_27_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨25, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 25 (by decide)))

theorem fz2_27_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨26, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 26 (by decide)))

theorem fz2_27_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨28, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 28 (by decide)))

theorem fz2_27_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨29, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 29 (by decide)))

theorem fz2_27_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨30, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 30 (by decide)))

theorem fz2_27_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨31, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 31 (by decide)))

theorem fz2_27_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨32, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 32 (by decide)))

theorem fz2_27_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨33, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 33 (by decide)))

theorem fz2_27_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨34, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 34 (by decide)))

theorem fz2_27_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨35, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 35 (by decide)))

theorem fz2_27_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨36, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 36 (by decide)))

theorem fz2_27_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨37, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 37 (by decide)))

theorem fz2_27_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨38, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 38 (by decide)))

theorem fz2_27_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨39, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 39 (by decide)))

theorem fz2_27_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨40, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 40 (by decide)))

theorem fz2_27_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨41, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 41 (by decide)))

theorem fz2_27_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨42, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 42 (by decide)))

theorem fz2_27_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨43, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 43 (by decide)))

theorem fz2_27_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨44, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 44 (by decide)))

theorem fz2_27_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨45, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 45 (by decide)))

theorem fz2_27_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨46, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 46 (by decide)))

theorem fz2_27_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨47, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 47 (by decide)))

theorem fz2_27_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨48, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 48 (by decide)))

theorem fz2_27_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨49, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 49 (by decide)))

theorem fz2_27_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨50, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 50 (by decide)))

theorem fz2_27_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨51, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 51 (by decide)))

theorem fz2_27_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨52, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 52 (by decide)))

theorem fz2_27_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨53, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 53 (by decide)))

theorem fz2_27_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK27)) = 0 :=
  Q2.repsFixedCard2 rK27 ⟨54, by decide⟩ Q2.R27_2 Q2.hpxR27_2 Q2.hcardq27_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_27) 54 (by decide)))

end LeanDring.P5Presentation
