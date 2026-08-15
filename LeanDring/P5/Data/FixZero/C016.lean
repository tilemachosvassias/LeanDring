/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C004

/-!
# Species-table cells, off-support emptiness certificates, chunk 15

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

theorem fixz1_16 : ([1, 6, 7, 8, 10, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK16) (retConj 1 (R16 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_16_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨1, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 1 (by decide)))

theorem fz1_16_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨6, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 6 (by decide)))

theorem fz1_16_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨7, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 7 (by decide)))

theorem fz1_16_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨8, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 8 (by decide)))

theorem fz1_16_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨10, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 10 (by decide)))

theorem fz1_16_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨12, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 12 (by decide)))

theorem fz1_16_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨13, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 13 (by decide)))

theorem fz1_16_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨14, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 14 (by decide)))

theorem fz1_16_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨15, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 15 (by decide)))

theorem fz1_16_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨17, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 17 (by decide)))

theorem fz1_16_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨18, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 18 (by decide)))

theorem fz1_16_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨19, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 19 (by decide)))

theorem fz1_16_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨20, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 20 (by decide)))

theorem fz1_16_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨21, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 21 (by decide)))

theorem fz1_16_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨22, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 22 (by decide)))

theorem fz1_16_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨23, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 23 (by decide)))

theorem fz1_16_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨24, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 24 (by decide)))

theorem fz1_16_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨25, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 25 (by decide)))

theorem fz1_16_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨26, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 26 (by decide)))

theorem fz1_16_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨27, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 27 (by decide)))

theorem fz1_16_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨28, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 28 (by decide)))

theorem fz1_16_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨29, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 29 (by decide)))

theorem fz1_16_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨30, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 30 (by decide)))

theorem fz1_16_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨31, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 31 (by decide)))

theorem fz1_16_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨32, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 32 (by decide)))

theorem fz1_16_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨33, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 33 (by decide)))

theorem fz1_16_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨34, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 34 (by decide)))

theorem fz1_16_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨35, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 35 (by decide)))

theorem fz1_16_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨36, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 36 (by decide)))

theorem fz1_16_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨37, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 37 (by decide)))

theorem fz1_16_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨38, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 38 (by decide)))

theorem fz1_16_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨39, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 39 (by decide)))

theorem fz1_16_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨40, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 40 (by decide)))

theorem fz1_16_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨41, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 41 (by decide)))

theorem fz1_16_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨42, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 42 (by decide)))

theorem fz1_16_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨43, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 43 (by decide)))

theorem fz1_16_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨44, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 44 (by decide)))

theorem fz1_16_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨45, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 45 (by decide)))

theorem fz1_16_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨46, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 46 (by decide)))

theorem fz1_16_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨47, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 47 (by decide)))

theorem fz1_16_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨48, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 48 (by decide)))

theorem fz1_16_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨49, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 49 (by decide)))

theorem fz1_16_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨50, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 50 (by decide)))

theorem fz1_16_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨51, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 51 (by decide)))

theorem fz1_16_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨52, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 52 (by decide)))

theorem fz1_16_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨53, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 53 (by decide)))

theorem fz1_16_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK16)) = 0 :=
  repsFixedCard rK16 ⟨54, by decide⟩ R16 hpxR16 hcardq16
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_16) 54 (by decide)))

theorem fixz2_16 : ([1, 6, 7, 8, 10, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK16) (retConj 2 (Q2.R16_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_16_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨1, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 1 (by decide)))

theorem fz2_16_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨6, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 6 (by decide)))

theorem fz2_16_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨7, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 7 (by decide)))

theorem fz2_16_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨8, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 8 (by decide)))

theorem fz2_16_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨10, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 10 (by decide)))

theorem fz2_16_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨12, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 12 (by decide)))

theorem fz2_16_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨13, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 13 (by decide)))

theorem fz2_16_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨14, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 14 (by decide)))

theorem fz2_16_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨15, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 15 (by decide)))

theorem fz2_16_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨17, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 17 (by decide)))

theorem fz2_16_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨18, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 18 (by decide)))

theorem fz2_16_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨19, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 19 (by decide)))

theorem fz2_16_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨20, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 20 (by decide)))

theorem fz2_16_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨21, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 21 (by decide)))

theorem fz2_16_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨22, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 22 (by decide)))

theorem fz2_16_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨23, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 23 (by decide)))

theorem fz2_16_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨24, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 24 (by decide)))

theorem fz2_16_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨25, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 25 (by decide)))

theorem fz2_16_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨26, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 26 (by decide)))

theorem fz2_16_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨27, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 27 (by decide)))

theorem fz2_16_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨28, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 28 (by decide)))

theorem fz2_16_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨29, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 29 (by decide)))

theorem fz2_16_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨30, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 30 (by decide)))

theorem fz2_16_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨31, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 31 (by decide)))

theorem fz2_16_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨32, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 32 (by decide)))

theorem fz2_16_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨33, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 33 (by decide)))

theorem fz2_16_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨34, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 34 (by decide)))

theorem fz2_16_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨35, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 35 (by decide)))

theorem fz2_16_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨36, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 36 (by decide)))

theorem fz2_16_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨37, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 37 (by decide)))

theorem fz2_16_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨38, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 38 (by decide)))

theorem fz2_16_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨39, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 39 (by decide)))

theorem fz2_16_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨40, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 40 (by decide)))

theorem fz2_16_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨41, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 41 (by decide)))

theorem fz2_16_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨42, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 42 (by decide)))

theorem fz2_16_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨43, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 43 (by decide)))

theorem fz2_16_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨44, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 44 (by decide)))

theorem fz2_16_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨45, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 45 (by decide)))

theorem fz2_16_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨46, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 46 (by decide)))

theorem fz2_16_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨47, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 47 (by decide)))

theorem fz2_16_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨48, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 48 (by decide)))

theorem fz2_16_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨49, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 49 (by decide)))

theorem fz2_16_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨50, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 50 (by decide)))

theorem fz2_16_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨51, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 51 (by decide)))

theorem fz2_16_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨52, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 52 (by decide)))

theorem fz2_16_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨53, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 53 (by decide)))

theorem fz2_16_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK16)) = 0 :=
  Q2.repsFixedCard2 rK16 ⟨54, by decide⟩ Q2.R16_2 Q2.hpxR16_2 Q2.hcardq16_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_16) 54 (by decide)))

end LeanDring.P5Presentation
