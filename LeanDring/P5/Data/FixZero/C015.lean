/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C003

/-!
# Species-table cells, off-support emptiness certificates, chunk 14

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

theorem fixz1_15 : ([1, 6, 7, 8, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK15) (retConj 1 (R15 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_15_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨1, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 1 (by decide)))

theorem fz1_15_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨6, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 6 (by decide)))

theorem fz1_15_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨7, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 7 (by decide)))

theorem fz1_15_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨8, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 8 (by decide)))

theorem fz1_15_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨10, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 10 (by decide)))

theorem fz1_15_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨12, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 12 (by decide)))

theorem fz1_15_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨13, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 13 (by decide)))

theorem fz1_15_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨14, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 14 (by decide)))

theorem fz1_15_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨16, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 16 (by decide)))

theorem fz1_15_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨17, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 17 (by decide)))

theorem fz1_15_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨18, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 18 (by decide)))

theorem fz1_15_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨19, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 19 (by decide)))

theorem fz1_15_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨20, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 20 (by decide)))

theorem fz1_15_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨21, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 21 (by decide)))

theorem fz1_15_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨22, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 22 (by decide)))

theorem fz1_15_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨23, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 23 (by decide)))

theorem fz1_15_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨24, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 24 (by decide)))

theorem fz1_15_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨25, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 25 (by decide)))

theorem fz1_15_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨26, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 26 (by decide)))

theorem fz1_15_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨27, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 27 (by decide)))

theorem fz1_15_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨28, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 28 (by decide)))

theorem fz1_15_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨29, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 29 (by decide)))

theorem fz1_15_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨30, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 30 (by decide)))

theorem fz1_15_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨31, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 31 (by decide)))

theorem fz1_15_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨32, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 32 (by decide)))

theorem fz1_15_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨33, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 33 (by decide)))

theorem fz1_15_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨34, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 34 (by decide)))

theorem fz1_15_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨35, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 35 (by decide)))

theorem fz1_15_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨36, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 36 (by decide)))

theorem fz1_15_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨37, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 37 (by decide)))

theorem fz1_15_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨38, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 38 (by decide)))

theorem fz1_15_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨39, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 39 (by decide)))

theorem fz1_15_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨40, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 40 (by decide)))

theorem fz1_15_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨41, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 41 (by decide)))

theorem fz1_15_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨42, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 42 (by decide)))

theorem fz1_15_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨43, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 43 (by decide)))

theorem fz1_15_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨44, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 44 (by decide)))

theorem fz1_15_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨45, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 45 (by decide)))

theorem fz1_15_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨46, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 46 (by decide)))

theorem fz1_15_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨47, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 47 (by decide)))

theorem fz1_15_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨48, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 48 (by decide)))

theorem fz1_15_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨49, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 49 (by decide)))

theorem fz1_15_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨50, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 50 (by decide)))

theorem fz1_15_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨51, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 51 (by decide)))

theorem fz1_15_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨52, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 52 (by decide)))

theorem fz1_15_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨53, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 53 (by decide)))

theorem fz1_15_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK15)) = 0 :=
  repsFixedCard rK15 ⟨54, by decide⟩ R15 hpxR15 hcardq15
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_15) 54 (by decide)))

theorem fixz2_15 : ([1, 6, 7, 8, 10, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK15) (retConj 2 (Q2.R15_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_15_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨1, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 1 (by decide)))

theorem fz2_15_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨6, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 6 (by decide)))

theorem fz2_15_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨7, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 7 (by decide)))

theorem fz2_15_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨8, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 8 (by decide)))

theorem fz2_15_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨10, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 10 (by decide)))

theorem fz2_15_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨12, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 12 (by decide)))

theorem fz2_15_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨13, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 13 (by decide)))

theorem fz2_15_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨14, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 14 (by decide)))

theorem fz2_15_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨16, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 16 (by decide)))

theorem fz2_15_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨17, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 17 (by decide)))

theorem fz2_15_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨18, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 18 (by decide)))

theorem fz2_15_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨19, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 19 (by decide)))

theorem fz2_15_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨20, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 20 (by decide)))

theorem fz2_15_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨21, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 21 (by decide)))

theorem fz2_15_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨22, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 22 (by decide)))

theorem fz2_15_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨23, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 23 (by decide)))

theorem fz2_15_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨24, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 24 (by decide)))

theorem fz2_15_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨25, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 25 (by decide)))

theorem fz2_15_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨26, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 26 (by decide)))

theorem fz2_15_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨27, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 27 (by decide)))

theorem fz2_15_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨28, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 28 (by decide)))

theorem fz2_15_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨29, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 29 (by decide)))

theorem fz2_15_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨30, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 30 (by decide)))

theorem fz2_15_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨31, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 31 (by decide)))

theorem fz2_15_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨32, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 32 (by decide)))

theorem fz2_15_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨33, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 33 (by decide)))

theorem fz2_15_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨34, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 34 (by decide)))

theorem fz2_15_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨35, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 35 (by decide)))

theorem fz2_15_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨36, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 36 (by decide)))

theorem fz2_15_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨37, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 37 (by decide)))

theorem fz2_15_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨38, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 38 (by decide)))

theorem fz2_15_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨39, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 39 (by decide)))

theorem fz2_15_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨40, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 40 (by decide)))

theorem fz2_15_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨41, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 41 (by decide)))

theorem fz2_15_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨42, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 42 (by decide)))

theorem fz2_15_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨43, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 43 (by decide)))

theorem fz2_15_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨44, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 44 (by decide)))

theorem fz2_15_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨45, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 45 (by decide)))

theorem fz2_15_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨46, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 46 (by decide)))

theorem fz2_15_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨47, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 47 (by decide)))

theorem fz2_15_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨48, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 48 (by decide)))

theorem fz2_15_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨49, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 49 (by decide)))

theorem fz2_15_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨50, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 50 (by decide)))

theorem fz2_15_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨51, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 51 (by decide)))

theorem fz2_15_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨52, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 52 (by decide)))

theorem fz2_15_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨53, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 53 (by decide)))

theorem fz2_15_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK15)) = 0 :=
  Q2.repsFixedCard2 rK15 ⟨54, by decide⟩ Q2.R15_2 Q2.hpxR15_2 Q2.hcardq15_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_15) 54 (by decide)))

end LeanDring.P5Presentation
