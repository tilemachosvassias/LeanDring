/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C030

/-!
# Species-table cells, off-support emptiness certificates, chunk 41

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

theorem fixz1_42 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK42) (retConj 1 (R42 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_42_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨1, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 1 (by decide)))

theorem fz1_42_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨2, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 2 (by decide)))

theorem fz1_42_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨3, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 3 (by decide)))

theorem fz1_42_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨4, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 4 (by decide)))

theorem fz1_42_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨5, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 5 (by decide)))

theorem fz1_42_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨6, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 6 (by decide)))

theorem fz1_42_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨7, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 7 (by decide)))

theorem fz1_42_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨8, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 8 (by decide)))

theorem fz1_42_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨9, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 9 (by decide)))

theorem fz1_42_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨10, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 10 (by decide)))

theorem fz1_42_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨11, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 11 (by decide)))

theorem fz1_42_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨13, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 13 (by decide)))

theorem fz1_42_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨14, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 14 (by decide)))

theorem fz1_42_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨15, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 15 (by decide)))

theorem fz1_42_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨16, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 16 (by decide)))

theorem fz1_42_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨17, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 17 (by decide)))

theorem fz1_42_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨18, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 18 (by decide)))

theorem fz1_42_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨19, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 19 (by decide)))

theorem fz1_42_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨20, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 20 (by decide)))

theorem fz1_42_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨21, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 21 (by decide)))

theorem fz1_42_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨22, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 22 (by decide)))

theorem fz1_42_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨23, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 23 (by decide)))

theorem fz1_42_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨24, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 24 (by decide)))

theorem fz1_42_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨25, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 25 (by decide)))

theorem fz1_42_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨26, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 26 (by decide)))

theorem fz1_42_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨27, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 27 (by decide)))

theorem fz1_42_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨28, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 28 (by decide)))

theorem fz1_42_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨29, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 29 (by decide)))

theorem fz1_42_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨30, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 30 (by decide)))

theorem fz1_42_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨31, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 31 (by decide)))

theorem fz1_42_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨32, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 32 (by decide)))

theorem fz1_42_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨33, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 33 (by decide)))

theorem fz1_42_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨34, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 34 (by decide)))

theorem fz1_42_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨35, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 35 (by decide)))

theorem fz1_42_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨36, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 36 (by decide)))

theorem fz1_42_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨37, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 37 (by decide)))

theorem fz1_42_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨38, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 38 (by decide)))

theorem fz1_42_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨39, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 39 (by decide)))

theorem fz1_42_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨40, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 40 (by decide)))

theorem fz1_42_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨41, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 41 (by decide)))

theorem fz1_42_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨43, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 43 (by decide)))

theorem fz1_42_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨44, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 44 (by decide)))

theorem fz1_42_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨45, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 45 (by decide)))

theorem fz1_42_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨46, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 46 (by decide)))

theorem fz1_42_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨47, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 47 (by decide)))

theorem fz1_42_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨48, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 48 (by decide)))

theorem fz1_42_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨49, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 49 (by decide)))

theorem fz1_42_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨50, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 50 (by decide)))

theorem fz1_42_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨51, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 51 (by decide)))

theorem fz1_42_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨52, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 52 (by decide)))

theorem fz1_42_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨53, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 53 (by decide)))

theorem fz1_42_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK42)) = 0 :=
  repsFixedCard rK42 ⟨54, by decide⟩ R42 hpxR42 hcardq42
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_42) 54 (by decide)))

theorem fixz2_42 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK42) (retConj 2 (Q2.R42_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_42_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨1, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 1 (by decide)))

theorem fz2_42_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨2, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 2 (by decide)))

theorem fz2_42_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨3, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 3 (by decide)))

theorem fz2_42_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨4, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 4 (by decide)))

theorem fz2_42_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨5, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 5 (by decide)))

theorem fz2_42_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨6, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 6 (by decide)))

theorem fz2_42_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨7, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 7 (by decide)))

theorem fz2_42_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨8, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 8 (by decide)))

theorem fz2_42_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨9, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 9 (by decide)))

theorem fz2_42_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨10, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 10 (by decide)))

theorem fz2_42_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨11, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 11 (by decide)))

theorem fz2_42_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨13, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 13 (by decide)))

theorem fz2_42_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨14, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 14 (by decide)))

theorem fz2_42_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨15, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 15 (by decide)))

theorem fz2_42_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨16, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 16 (by decide)))

theorem fz2_42_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨17, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 17 (by decide)))

theorem fz2_42_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨18, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 18 (by decide)))

theorem fz2_42_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨19, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 19 (by decide)))

theorem fz2_42_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨20, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 20 (by decide)))

theorem fz2_42_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨21, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 21 (by decide)))

theorem fz2_42_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨22, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 22 (by decide)))

theorem fz2_42_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨23, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 23 (by decide)))

theorem fz2_42_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨24, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 24 (by decide)))

theorem fz2_42_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨25, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 25 (by decide)))

theorem fz2_42_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨26, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 26 (by decide)))

theorem fz2_42_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨27, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 27 (by decide)))

theorem fz2_42_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨28, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 28 (by decide)))

theorem fz2_42_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨29, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 29 (by decide)))

theorem fz2_42_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨30, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 30 (by decide)))

theorem fz2_42_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨31, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 31 (by decide)))

theorem fz2_42_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨32, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 32 (by decide)))

theorem fz2_42_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨33, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 33 (by decide)))

theorem fz2_42_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨34, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 34 (by decide)))

theorem fz2_42_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨35, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 35 (by decide)))

theorem fz2_42_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨36, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 36 (by decide)))

theorem fz2_42_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨37, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 37 (by decide)))

theorem fz2_42_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨38, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 38 (by decide)))

theorem fz2_42_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨39, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 39 (by decide)))

theorem fz2_42_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨40, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 40 (by decide)))

theorem fz2_42_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨41, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 41 (by decide)))

theorem fz2_42_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨43, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 43 (by decide)))

theorem fz2_42_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨44, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 44 (by decide)))

theorem fz2_42_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨45, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 45 (by decide)))

theorem fz2_42_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨46, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 46 (by decide)))

theorem fz2_42_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨47, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 47 (by decide)))

theorem fz2_42_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨48, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 48 (by decide)))

theorem fz2_42_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨49, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 49 (by decide)))

theorem fz2_42_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨50, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 50 (by decide)))

theorem fz2_42_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨51, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 51 (by decide)))

theorem fz2_42_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨52, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 52 (by decide)))

theorem fz2_42_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨53, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 53 (by decide)))

theorem fz2_42_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK42)) = 0 :=
  Q2.repsFixedCard2 rK42 ⟨54, by decide⟩ Q2.R42_2 Q2.hpxR42_2 Q2.hcardq42_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_42) 54 (by decide)))

end LeanDring.P5Presentation
