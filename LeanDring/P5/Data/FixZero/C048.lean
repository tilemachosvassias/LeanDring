/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C036

/-!
# Species-table cells, off-support emptiness certificates, chunk 47

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

theorem fixz1_48 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK48) (retConj 1 (R48 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_48_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨1, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 1 (by decide)))

theorem fz1_48_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨2, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 2 (by decide)))

theorem fz1_48_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨3, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 3 (by decide)))

theorem fz1_48_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨4, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 4 (by decide)))

theorem fz1_48_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨5, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 5 (by decide)))

theorem fz1_48_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨6, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 6 (by decide)))

theorem fz1_48_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨7, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 7 (by decide)))

theorem fz1_48_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨8, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 8 (by decide)))

theorem fz1_48_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨9, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 9 (by decide)))

theorem fz1_48_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨10, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 10 (by decide)))

theorem fz1_48_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨11, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 11 (by decide)))

theorem fz1_48_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨13, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 13 (by decide)))

theorem fz1_48_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨14, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 14 (by decide)))

theorem fz1_48_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨15, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 15 (by decide)))

theorem fz1_48_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨16, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 16 (by decide)))

theorem fz1_48_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨17, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 17 (by decide)))

theorem fz1_48_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨18, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 18 (by decide)))

theorem fz1_48_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨19, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 19 (by decide)))

theorem fz1_48_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨20, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 20 (by decide)))

theorem fz1_48_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨21, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 21 (by decide)))

theorem fz1_48_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨22, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 22 (by decide)))

theorem fz1_48_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨23, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 23 (by decide)))

theorem fz1_48_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨24, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 24 (by decide)))

theorem fz1_48_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨25, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 25 (by decide)))

theorem fz1_48_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨26, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 26 (by decide)))

theorem fz1_48_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨27, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 27 (by decide)))

theorem fz1_48_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨28, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 28 (by decide)))

theorem fz1_48_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨29, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 29 (by decide)))

theorem fz1_48_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨30, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 30 (by decide)))

theorem fz1_48_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨31, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 31 (by decide)))

theorem fz1_48_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨32, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 32 (by decide)))

theorem fz1_48_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨33, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 33 (by decide)))

theorem fz1_48_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨34, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 34 (by decide)))

theorem fz1_48_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨35, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 35 (by decide)))

theorem fz1_48_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨36, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 36 (by decide)))

theorem fz1_48_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨37, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 37 (by decide)))

theorem fz1_48_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨38, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 38 (by decide)))

theorem fz1_48_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨39, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 39 (by decide)))

theorem fz1_48_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨40, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 40 (by decide)))

theorem fz1_48_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨41, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 41 (by decide)))

theorem fz1_48_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨42, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 42 (by decide)))

theorem fz1_48_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨43, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 43 (by decide)))

theorem fz1_48_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨44, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 44 (by decide)))

theorem fz1_48_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨45, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 45 (by decide)))

theorem fz1_48_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨46, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 46 (by decide)))

theorem fz1_48_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨47, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 47 (by decide)))

theorem fz1_48_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨49, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 49 (by decide)))

theorem fz1_48_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨50, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 50 (by decide)))

theorem fz1_48_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨51, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 51 (by decide)))

theorem fz1_48_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨52, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 52 (by decide)))

theorem fz1_48_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨53, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 53 (by decide)))

theorem fz1_48_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK48)) = 0 :=
  repsFixedCard rK48 ⟨54, by decide⟩ R48 hpxR48 hcardq48
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_48) 54 (by decide)))

theorem fixz2_48 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK48) (retConj 2 (Q2.R48_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_48_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨1, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 1 (by decide)))

theorem fz2_48_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨2, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 2 (by decide)))

theorem fz2_48_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨3, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 3 (by decide)))

theorem fz2_48_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨4, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 4 (by decide)))

theorem fz2_48_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨5, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 5 (by decide)))

theorem fz2_48_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨6, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 6 (by decide)))

theorem fz2_48_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨7, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 7 (by decide)))

theorem fz2_48_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨8, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 8 (by decide)))

theorem fz2_48_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨9, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 9 (by decide)))

theorem fz2_48_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨10, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 10 (by decide)))

theorem fz2_48_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨11, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 11 (by decide)))

theorem fz2_48_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨13, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 13 (by decide)))

theorem fz2_48_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨14, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 14 (by decide)))

theorem fz2_48_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨15, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 15 (by decide)))

theorem fz2_48_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨16, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 16 (by decide)))

theorem fz2_48_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨17, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 17 (by decide)))

theorem fz2_48_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨18, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 18 (by decide)))

theorem fz2_48_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨19, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 19 (by decide)))

theorem fz2_48_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨20, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 20 (by decide)))

theorem fz2_48_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨21, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 21 (by decide)))

theorem fz2_48_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨22, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 22 (by decide)))

theorem fz2_48_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨23, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 23 (by decide)))

theorem fz2_48_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨24, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 24 (by decide)))

theorem fz2_48_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨25, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 25 (by decide)))

theorem fz2_48_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨26, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 26 (by decide)))

theorem fz2_48_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨27, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 27 (by decide)))

theorem fz2_48_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨28, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 28 (by decide)))

theorem fz2_48_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨29, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 29 (by decide)))

theorem fz2_48_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨30, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 30 (by decide)))

theorem fz2_48_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨31, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 31 (by decide)))

theorem fz2_48_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨32, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 32 (by decide)))

theorem fz2_48_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨33, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 33 (by decide)))

theorem fz2_48_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨34, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 34 (by decide)))

theorem fz2_48_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨35, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 35 (by decide)))

theorem fz2_48_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨36, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 36 (by decide)))

theorem fz2_48_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨37, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 37 (by decide)))

theorem fz2_48_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨38, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 38 (by decide)))

theorem fz2_48_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨39, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 39 (by decide)))

theorem fz2_48_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨40, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 40 (by decide)))

theorem fz2_48_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨41, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 41 (by decide)))

theorem fz2_48_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨42, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 42 (by decide)))

theorem fz2_48_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨43, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 43 (by decide)))

theorem fz2_48_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨44, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 44 (by decide)))

theorem fz2_48_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨45, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 45 (by decide)))

theorem fz2_48_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨46, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 46 (by decide)))

theorem fz2_48_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨47, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 47 (by decide)))

theorem fz2_48_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨49, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 49 (by decide)))

theorem fz2_48_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨50, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 50 (by decide)))

theorem fz2_48_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨51, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 51 (by decide)))

theorem fz2_48_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨52, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 52 (by decide)))

theorem fz2_48_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨53, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 53 (by decide)))

theorem fz2_48_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK48)) = 0 :=
  Q2.repsFixedCard2 rK48 ⟨54, by decide⟩ Q2.R48_2 Q2.hpxR48_2 Q2.hcardq48_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_48) 54 (by decide)))

end LeanDring.P5Presentation
