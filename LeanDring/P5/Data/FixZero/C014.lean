/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C002

/-!
# Species-table cells, off-support emptiness certificates, chunk 13

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

theorem fixz1_14 : ([1, 6, 7, 8, 10, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK14) (retConj 1 (R14 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_14_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨1, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 1 (by decide)))

theorem fz1_14_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨6, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 6 (by decide)))

theorem fz1_14_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨7, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 7 (by decide)))

theorem fz1_14_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨8, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 8 (by decide)))

theorem fz1_14_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨10, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 10 (by decide)))

theorem fz1_14_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨12, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 12 (by decide)))

theorem fz1_14_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨13, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 13 (by decide)))

theorem fz1_14_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨15, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 15 (by decide)))

theorem fz1_14_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨16, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 16 (by decide)))

theorem fz1_14_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨17, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 17 (by decide)))

theorem fz1_14_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨18, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 18 (by decide)))

theorem fz1_14_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨19, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 19 (by decide)))

theorem fz1_14_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨20, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 20 (by decide)))

theorem fz1_14_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨21, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 21 (by decide)))

theorem fz1_14_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨22, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 22 (by decide)))

theorem fz1_14_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨23, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 23 (by decide)))

theorem fz1_14_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨24, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 24 (by decide)))

theorem fz1_14_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨25, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 25 (by decide)))

theorem fz1_14_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨26, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 26 (by decide)))

theorem fz1_14_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨27, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 27 (by decide)))

theorem fz1_14_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨28, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 28 (by decide)))

theorem fz1_14_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨29, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 29 (by decide)))

theorem fz1_14_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨30, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 30 (by decide)))

theorem fz1_14_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨31, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 31 (by decide)))

theorem fz1_14_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨32, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 32 (by decide)))

theorem fz1_14_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨33, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 33 (by decide)))

theorem fz1_14_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨34, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 34 (by decide)))

theorem fz1_14_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨35, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 35 (by decide)))

theorem fz1_14_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨36, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 36 (by decide)))

theorem fz1_14_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨37, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 37 (by decide)))

theorem fz1_14_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨38, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 38 (by decide)))

theorem fz1_14_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨39, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 39 (by decide)))

theorem fz1_14_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨40, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 40 (by decide)))

theorem fz1_14_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨41, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 41 (by decide)))

theorem fz1_14_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨42, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 42 (by decide)))

theorem fz1_14_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨43, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 43 (by decide)))

theorem fz1_14_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨44, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 44 (by decide)))

theorem fz1_14_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨45, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 45 (by decide)))

theorem fz1_14_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨46, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 46 (by decide)))

theorem fz1_14_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨47, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 47 (by decide)))

theorem fz1_14_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨48, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 48 (by decide)))

theorem fz1_14_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨49, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 49 (by decide)))

theorem fz1_14_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨50, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 50 (by decide)))

theorem fz1_14_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨51, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 51 (by decide)))

theorem fz1_14_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨52, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 52 (by decide)))

theorem fz1_14_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨53, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 53 (by decide)))

theorem fz1_14_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK14)) = 0 :=
  repsFixedCard rK14 ⟨54, by decide⟩ R14 hpxR14 hcardq14
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_14) 54 (by decide)))

theorem fixz2_14 : ([1, 6, 7, 8, 10, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK14) (retConj 2 (Q2.R14_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_14_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨1, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 1 (by decide)))

theorem fz2_14_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨6, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 6 (by decide)))

theorem fz2_14_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨7, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 7 (by decide)))

theorem fz2_14_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨8, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 8 (by decide)))

theorem fz2_14_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨10, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 10 (by decide)))

theorem fz2_14_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨12, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 12 (by decide)))

theorem fz2_14_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨13, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 13 (by decide)))

theorem fz2_14_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨15, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 15 (by decide)))

theorem fz2_14_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨16, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 16 (by decide)))

theorem fz2_14_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨17, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 17 (by decide)))

theorem fz2_14_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨18, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 18 (by decide)))

theorem fz2_14_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨19, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 19 (by decide)))

theorem fz2_14_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨20, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 20 (by decide)))

theorem fz2_14_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨21, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 21 (by decide)))

theorem fz2_14_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨22, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 22 (by decide)))

theorem fz2_14_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨23, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 23 (by decide)))

theorem fz2_14_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨24, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 24 (by decide)))

theorem fz2_14_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨25, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 25 (by decide)))

theorem fz2_14_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨26, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 26 (by decide)))

theorem fz2_14_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨27, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 27 (by decide)))

theorem fz2_14_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨28, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 28 (by decide)))

theorem fz2_14_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨29, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 29 (by decide)))

theorem fz2_14_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨30, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 30 (by decide)))

theorem fz2_14_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨31, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 31 (by decide)))

theorem fz2_14_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨32, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 32 (by decide)))

theorem fz2_14_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨33, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 33 (by decide)))

theorem fz2_14_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨34, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 34 (by decide)))

theorem fz2_14_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨35, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 35 (by decide)))

theorem fz2_14_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨36, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 36 (by decide)))

theorem fz2_14_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨37, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 37 (by decide)))

theorem fz2_14_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨38, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 38 (by decide)))

theorem fz2_14_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨39, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 39 (by decide)))

theorem fz2_14_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨40, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 40 (by decide)))

theorem fz2_14_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨41, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 41 (by decide)))

theorem fz2_14_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨42, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 42 (by decide)))

theorem fz2_14_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨43, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 43 (by decide)))

theorem fz2_14_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨44, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 44 (by decide)))

theorem fz2_14_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨45, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 45 (by decide)))

theorem fz2_14_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨46, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 46 (by decide)))

theorem fz2_14_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨47, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 47 (by decide)))

theorem fz2_14_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨48, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 48 (by decide)))

theorem fz2_14_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨49, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 49 (by decide)))

theorem fz2_14_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨50, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 50 (by decide)))

theorem fz2_14_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨51, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 51 (by decide)))

theorem fz2_14_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨52, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 52 (by decide)))

theorem fz2_14_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨53, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 53 (by decide)))

theorem fz2_14_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK14)) = 0 :=
  Q2.repsFixedCard2 rK14 ⟨54, by decide⟩ Q2.R14_2 Q2.hpxR14_2 Q2.hcardq14_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_14) 54 (by decide)))

end LeanDring.P5Presentation
