/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C024

/-!
# Species-table cells, off-support emptiness certificates, chunk 35

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

theorem fixz1_36 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK36) (retConj 1 (R36 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_36_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨1, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 1 (by decide)))

theorem fz1_36_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨2, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 2 (by decide)))

theorem fz1_36_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨3, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 3 (by decide)))

theorem fz1_36_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨4, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 4 (by decide)))

theorem fz1_36_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨5, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 5 (by decide)))

theorem fz1_36_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨6, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 6 (by decide)))

theorem fz1_36_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨7, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 7 (by decide)))

theorem fz1_36_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨8, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 8 (by decide)))

theorem fz1_36_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨9, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 9 (by decide)))

theorem fz1_36_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨10, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 10 (by decide)))

theorem fz1_36_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨11, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 11 (by decide)))

theorem fz1_36_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨13, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 13 (by decide)))

theorem fz1_36_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨14, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 14 (by decide)))

theorem fz1_36_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨15, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 15 (by decide)))

theorem fz1_36_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨16, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 16 (by decide)))

theorem fz1_36_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨17, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 17 (by decide)))

theorem fz1_36_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨18, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 18 (by decide)))

theorem fz1_36_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨19, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 19 (by decide)))

theorem fz1_36_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨20, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 20 (by decide)))

theorem fz1_36_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨21, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 21 (by decide)))

theorem fz1_36_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨22, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 22 (by decide)))

theorem fz1_36_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨23, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 23 (by decide)))

theorem fz1_36_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨24, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 24 (by decide)))

theorem fz1_36_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨25, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 25 (by decide)))

theorem fz1_36_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨26, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 26 (by decide)))

theorem fz1_36_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨27, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 27 (by decide)))

theorem fz1_36_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨28, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 28 (by decide)))

theorem fz1_36_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨29, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 29 (by decide)))

theorem fz1_36_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨30, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 30 (by decide)))

theorem fz1_36_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨31, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 31 (by decide)))

theorem fz1_36_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨32, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 32 (by decide)))

theorem fz1_36_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨33, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 33 (by decide)))

theorem fz1_36_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨34, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 34 (by decide)))

theorem fz1_36_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨35, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 35 (by decide)))

theorem fz1_36_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨37, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 37 (by decide)))

theorem fz1_36_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨38, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 38 (by decide)))

theorem fz1_36_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨39, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 39 (by decide)))

theorem fz1_36_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨40, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 40 (by decide)))

theorem fz1_36_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨41, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 41 (by decide)))

theorem fz1_36_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨42, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 42 (by decide)))

theorem fz1_36_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨43, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 43 (by decide)))

theorem fz1_36_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨44, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 44 (by decide)))

theorem fz1_36_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨45, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 45 (by decide)))

theorem fz1_36_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨46, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 46 (by decide)))

theorem fz1_36_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨47, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 47 (by decide)))

theorem fz1_36_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨48, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 48 (by decide)))

theorem fz1_36_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨49, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 49 (by decide)))

theorem fz1_36_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨50, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 50 (by decide)))

theorem fz1_36_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨51, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 51 (by decide)))

theorem fz1_36_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨52, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 52 (by decide)))

theorem fz1_36_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨53, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 53 (by decide)))

theorem fz1_36_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK36)) = 0 :=
  repsFixedCard rK36 ⟨54, by decide⟩ R36 hpxR36 hcardq36
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_36) 54 (by decide)))

theorem fixz2_36 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK36) (retConj 2 (Q2.R36_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_36_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨1, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 1 (by decide)))

theorem fz2_36_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨2, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 2 (by decide)))

theorem fz2_36_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨3, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 3 (by decide)))

theorem fz2_36_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨4, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 4 (by decide)))

theorem fz2_36_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨5, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 5 (by decide)))

theorem fz2_36_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨6, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 6 (by decide)))

theorem fz2_36_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨7, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 7 (by decide)))

theorem fz2_36_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨8, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 8 (by decide)))

theorem fz2_36_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨9, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 9 (by decide)))

theorem fz2_36_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨10, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 10 (by decide)))

theorem fz2_36_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨11, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 11 (by decide)))

theorem fz2_36_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨13, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 13 (by decide)))

theorem fz2_36_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨14, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 14 (by decide)))

theorem fz2_36_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨15, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 15 (by decide)))

theorem fz2_36_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨16, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 16 (by decide)))

theorem fz2_36_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨17, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 17 (by decide)))

theorem fz2_36_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨18, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 18 (by decide)))

theorem fz2_36_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨19, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 19 (by decide)))

theorem fz2_36_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨20, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 20 (by decide)))

theorem fz2_36_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨21, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 21 (by decide)))

theorem fz2_36_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨22, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 22 (by decide)))

theorem fz2_36_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨23, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 23 (by decide)))

theorem fz2_36_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨24, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 24 (by decide)))

theorem fz2_36_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨25, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 25 (by decide)))

theorem fz2_36_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨26, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 26 (by decide)))

theorem fz2_36_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨27, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 27 (by decide)))

theorem fz2_36_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨28, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 28 (by decide)))

theorem fz2_36_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨29, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 29 (by decide)))

theorem fz2_36_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨30, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 30 (by decide)))

theorem fz2_36_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨31, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 31 (by decide)))

theorem fz2_36_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨32, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 32 (by decide)))

theorem fz2_36_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨33, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 33 (by decide)))

theorem fz2_36_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨34, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 34 (by decide)))

theorem fz2_36_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨35, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 35 (by decide)))

theorem fz2_36_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨37, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 37 (by decide)))

theorem fz2_36_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨38, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 38 (by decide)))

theorem fz2_36_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨39, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 39 (by decide)))

theorem fz2_36_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨40, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 40 (by decide)))

theorem fz2_36_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨41, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 41 (by decide)))

theorem fz2_36_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨42, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 42 (by decide)))

theorem fz2_36_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨43, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 43 (by decide)))

theorem fz2_36_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨44, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 44 (by decide)))

theorem fz2_36_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨45, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 45 (by decide)))

theorem fz2_36_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨46, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 46 (by decide)))

theorem fz2_36_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨47, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 47 (by decide)))

theorem fz2_36_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨48, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 48 (by decide)))

theorem fz2_36_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨49, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 49 (by decide)))

theorem fz2_36_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨50, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 50 (by decide)))

theorem fz2_36_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨51, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 51 (by decide)))

theorem fz2_36_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨52, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 52 (by decide)))

theorem fz2_36_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨53, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 53 (by decide)))

theorem fz2_36_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK36)) = 0 :=
  Q2.repsFixedCard2 rK36 ⟨54, by decide⟩ Q2.R36_2 Q2.hpxR36_2 Q2.hcardq36_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_36) 54 (by decide)))

end LeanDring.P5Presentation
