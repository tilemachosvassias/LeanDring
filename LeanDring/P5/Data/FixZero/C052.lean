/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C040

/-!
# Species-table cells, off-support emptiness certificates, chunk 51

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

theorem fixz1_52 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK52) (retConj 1 (R52 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_52_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨1, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 1 (by decide)))

theorem fz1_52_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨2, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 2 (by decide)))

theorem fz1_52_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨3, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 3 (by decide)))

theorem fz1_52_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨4, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 4 (by decide)))

theorem fz1_52_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨5, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 5 (by decide)))

theorem fz1_52_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨6, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 6 (by decide)))

theorem fz1_52_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨7, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 7 (by decide)))

theorem fz1_52_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨8, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 8 (by decide)))

theorem fz1_52_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨9, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 9 (by decide)))

theorem fz1_52_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨10, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 10 (by decide)))

theorem fz1_52_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨11, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 11 (by decide)))

theorem fz1_52_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨13, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 13 (by decide)))

theorem fz1_52_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨14, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 14 (by decide)))

theorem fz1_52_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨15, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 15 (by decide)))

theorem fz1_52_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨16, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 16 (by decide)))

theorem fz1_52_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨17, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 17 (by decide)))

theorem fz1_52_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨18, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 18 (by decide)))

theorem fz1_52_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨19, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 19 (by decide)))

theorem fz1_52_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨20, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 20 (by decide)))

theorem fz1_52_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨21, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 21 (by decide)))

theorem fz1_52_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨22, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 22 (by decide)))

theorem fz1_52_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨23, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 23 (by decide)))

theorem fz1_52_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨24, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 24 (by decide)))

theorem fz1_52_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨25, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 25 (by decide)))

theorem fz1_52_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨26, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 26 (by decide)))

theorem fz1_52_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨27, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 27 (by decide)))

theorem fz1_52_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨28, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 28 (by decide)))

theorem fz1_52_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨29, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 29 (by decide)))

theorem fz1_52_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨30, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 30 (by decide)))

theorem fz1_52_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨31, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 31 (by decide)))

theorem fz1_52_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨32, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 32 (by decide)))

theorem fz1_52_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨33, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 33 (by decide)))

theorem fz1_52_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨34, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 34 (by decide)))

theorem fz1_52_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨35, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 35 (by decide)))

theorem fz1_52_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨36, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 36 (by decide)))

theorem fz1_52_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨37, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 37 (by decide)))

theorem fz1_52_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨38, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 38 (by decide)))

theorem fz1_52_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨39, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 39 (by decide)))

theorem fz1_52_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨40, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 40 (by decide)))

theorem fz1_52_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨41, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 41 (by decide)))

theorem fz1_52_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨42, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 42 (by decide)))

theorem fz1_52_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨43, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 43 (by decide)))

theorem fz1_52_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨44, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 44 (by decide)))

theorem fz1_52_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨45, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 45 (by decide)))

theorem fz1_52_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨46, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 46 (by decide)))

theorem fz1_52_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨47, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 47 (by decide)))

theorem fz1_52_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨48, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 48 (by decide)))

theorem fz1_52_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨49, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 49 (by decide)))

theorem fz1_52_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨50, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 50 (by decide)))

theorem fz1_52_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨51, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 51 (by decide)))

theorem fz1_52_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨53, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 53 (by decide)))

theorem fz1_52_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK52)) = 0 :=
  repsFixedCard rK52 ⟨54, by decide⟩ R52 hpxR52 hcardq52
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_52) 54 (by decide)))

theorem fixz2_52 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK52) (retConj 2 (Q2.R52_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_52_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨1, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 1 (by decide)))

theorem fz2_52_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨2, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 2 (by decide)))

theorem fz2_52_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨3, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 3 (by decide)))

theorem fz2_52_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨4, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 4 (by decide)))

theorem fz2_52_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨5, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 5 (by decide)))

theorem fz2_52_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨6, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 6 (by decide)))

theorem fz2_52_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨7, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 7 (by decide)))

theorem fz2_52_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨8, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 8 (by decide)))

theorem fz2_52_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨9, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 9 (by decide)))

theorem fz2_52_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨10, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 10 (by decide)))

theorem fz2_52_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨11, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 11 (by decide)))

theorem fz2_52_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨13, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 13 (by decide)))

theorem fz2_52_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨14, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 14 (by decide)))

theorem fz2_52_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨15, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 15 (by decide)))

theorem fz2_52_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨16, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 16 (by decide)))

theorem fz2_52_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨17, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 17 (by decide)))

theorem fz2_52_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨18, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 18 (by decide)))

theorem fz2_52_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨19, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 19 (by decide)))

theorem fz2_52_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨20, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 20 (by decide)))

theorem fz2_52_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨21, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 21 (by decide)))

theorem fz2_52_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨22, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 22 (by decide)))

theorem fz2_52_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨23, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 23 (by decide)))

theorem fz2_52_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨24, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 24 (by decide)))

theorem fz2_52_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨25, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 25 (by decide)))

theorem fz2_52_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨26, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 26 (by decide)))

theorem fz2_52_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨27, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 27 (by decide)))

theorem fz2_52_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨28, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 28 (by decide)))

theorem fz2_52_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨29, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 29 (by decide)))

theorem fz2_52_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨30, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 30 (by decide)))

theorem fz2_52_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨31, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 31 (by decide)))

theorem fz2_52_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨32, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 32 (by decide)))

theorem fz2_52_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨33, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 33 (by decide)))

theorem fz2_52_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨34, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 34 (by decide)))

theorem fz2_52_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨35, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 35 (by decide)))

theorem fz2_52_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨36, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 36 (by decide)))

theorem fz2_52_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨37, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 37 (by decide)))

theorem fz2_52_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨38, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 38 (by decide)))

theorem fz2_52_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨39, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 39 (by decide)))

theorem fz2_52_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨40, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 40 (by decide)))

theorem fz2_52_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨41, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 41 (by decide)))

theorem fz2_52_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨42, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 42 (by decide)))

theorem fz2_52_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨43, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 43 (by decide)))

theorem fz2_52_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨44, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 44 (by decide)))

theorem fz2_52_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨45, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 45 (by decide)))

theorem fz2_52_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨46, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 46 (by decide)))

theorem fz2_52_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨47, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 47 (by decide)))

theorem fz2_52_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨48, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 48 (by decide)))

theorem fz2_52_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨49, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 49 (by decide)))

theorem fz2_52_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨50, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 50 (by decide)))

theorem fz2_52_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨51, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 51 (by decide)))

theorem fz2_52_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨53, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 53 (by decide)))

theorem fz2_52_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK52)) = 0 :=
  Q2.repsFixedCard2 rK52 ⟨54, by decide⟩ Q2.R52_2 Q2.hpxR52_2 Q2.hcardq52_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_52) 54 (by decide)))

end LeanDring.P5Presentation
