/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C005

/-!
# Species-table cells, off-support emptiness certificates, chunk 16

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

theorem fixz1_17 : ([1, 6, 7, 8, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK17) (retConj 1 (R17 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_17_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨1, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 1 (by decide)))

theorem fz1_17_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨6, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 6 (by decide)))

theorem fz1_17_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨7, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 7 (by decide)))

theorem fz1_17_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨8, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 8 (by decide)))

theorem fz1_17_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨10, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 10 (by decide)))

theorem fz1_17_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨12, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 12 (by decide)))

theorem fz1_17_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨13, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 13 (by decide)))

theorem fz1_17_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨14, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 14 (by decide)))

theorem fz1_17_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨15, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 15 (by decide)))

theorem fz1_17_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨16, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 16 (by decide)))

theorem fz1_17_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨18, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 18 (by decide)))

theorem fz1_17_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨19, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 19 (by decide)))

theorem fz1_17_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨20, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 20 (by decide)))

theorem fz1_17_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨21, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 21 (by decide)))

theorem fz1_17_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨22, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 22 (by decide)))

theorem fz1_17_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨23, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 23 (by decide)))

theorem fz1_17_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨24, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 24 (by decide)))

theorem fz1_17_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨25, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 25 (by decide)))

theorem fz1_17_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨26, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 26 (by decide)))

theorem fz1_17_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨27, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 27 (by decide)))

theorem fz1_17_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨28, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 28 (by decide)))

theorem fz1_17_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨29, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 29 (by decide)))

theorem fz1_17_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨30, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 30 (by decide)))

theorem fz1_17_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨31, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 31 (by decide)))

theorem fz1_17_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨32, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 32 (by decide)))

theorem fz1_17_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨33, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 33 (by decide)))

theorem fz1_17_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨34, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 34 (by decide)))

theorem fz1_17_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨35, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 35 (by decide)))

theorem fz1_17_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨36, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 36 (by decide)))

theorem fz1_17_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨37, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 37 (by decide)))

theorem fz1_17_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨38, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 38 (by decide)))

theorem fz1_17_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨39, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 39 (by decide)))

theorem fz1_17_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨40, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 40 (by decide)))

theorem fz1_17_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨41, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 41 (by decide)))

theorem fz1_17_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨42, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 42 (by decide)))

theorem fz1_17_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨43, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 43 (by decide)))

theorem fz1_17_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨44, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 44 (by decide)))

theorem fz1_17_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨45, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 45 (by decide)))

theorem fz1_17_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨46, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 46 (by decide)))

theorem fz1_17_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨47, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 47 (by decide)))

theorem fz1_17_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨48, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 48 (by decide)))

theorem fz1_17_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨49, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 49 (by decide)))

theorem fz1_17_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨50, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 50 (by decide)))

theorem fz1_17_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨51, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 51 (by decide)))

theorem fz1_17_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨52, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 52 (by decide)))

theorem fz1_17_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨53, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 53 (by decide)))

theorem fz1_17_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK17)) = 0 :=
  repsFixedCard rK17 ⟨54, by decide⟩ R17 hpxR17 hcardq17
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_17) 54 (by decide)))

theorem fixz2_17 : ([1, 6, 7, 8, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK17) (retConj 2 (Q2.R17_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_17_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨1, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 1 (by decide)))

theorem fz2_17_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨6, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 6 (by decide)))

theorem fz2_17_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨7, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 7 (by decide)))

theorem fz2_17_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨8, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 8 (by decide)))

theorem fz2_17_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨10, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 10 (by decide)))

theorem fz2_17_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨12, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 12 (by decide)))

theorem fz2_17_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨13, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 13 (by decide)))

theorem fz2_17_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨14, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 14 (by decide)))

theorem fz2_17_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨15, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 15 (by decide)))

theorem fz2_17_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨16, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 16 (by decide)))

theorem fz2_17_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨18, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 18 (by decide)))

theorem fz2_17_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨19, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 19 (by decide)))

theorem fz2_17_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨20, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 20 (by decide)))

theorem fz2_17_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨21, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 21 (by decide)))

theorem fz2_17_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨22, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 22 (by decide)))

theorem fz2_17_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨23, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 23 (by decide)))

theorem fz2_17_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨24, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 24 (by decide)))

theorem fz2_17_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨25, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 25 (by decide)))

theorem fz2_17_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨26, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 26 (by decide)))

theorem fz2_17_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨27, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 27 (by decide)))

theorem fz2_17_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨28, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 28 (by decide)))

theorem fz2_17_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨29, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 29 (by decide)))

theorem fz2_17_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨30, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 30 (by decide)))

theorem fz2_17_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨31, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 31 (by decide)))

theorem fz2_17_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨32, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 32 (by decide)))

theorem fz2_17_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨33, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 33 (by decide)))

theorem fz2_17_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨34, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 34 (by decide)))

theorem fz2_17_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨35, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 35 (by decide)))

theorem fz2_17_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨36, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 36 (by decide)))

theorem fz2_17_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨37, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 37 (by decide)))

theorem fz2_17_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨38, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 38 (by decide)))

theorem fz2_17_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨39, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 39 (by decide)))

theorem fz2_17_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨40, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 40 (by decide)))

theorem fz2_17_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨41, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 41 (by decide)))

theorem fz2_17_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨42, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 42 (by decide)))

theorem fz2_17_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨43, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 43 (by decide)))

theorem fz2_17_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨44, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 44 (by decide)))

theorem fz2_17_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨45, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 45 (by decide)))

theorem fz2_17_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨46, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 46 (by decide)))

theorem fz2_17_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨47, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 47 (by decide)))

theorem fz2_17_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨48, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 48 (by decide)))

theorem fz2_17_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨49, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 49 (by decide)))

theorem fz2_17_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨50, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 50 (by decide)))

theorem fz2_17_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨51, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 51 (by decide)))

theorem fz2_17_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨52, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 52 (by decide)))

theorem fz2_17_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨53, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 53 (by decide)))

theorem fz2_17_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK17)) = 0 :=
  Q2.repsFixedCard2 rK17 ⟨54, by decide⟩ Q2.R17_2 Q2.hpxR17_2 Q2.hcardq17_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_17) 54 (by decide)))

end LeanDring.P5Presentation
