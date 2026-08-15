/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C037

/-!
# Species-table cells, off-support emptiness certificates, chunk 48

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

theorem fixz1_49 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK49) (retConj 1 (R49 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_49_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨1, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 1 (by decide)))

theorem fz1_49_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨2, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 2 (by decide)))

theorem fz1_49_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨3, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 3 (by decide)))

theorem fz1_49_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨4, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 4 (by decide)))

theorem fz1_49_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨5, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 5 (by decide)))

theorem fz1_49_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨6, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 6 (by decide)))

theorem fz1_49_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨7, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 7 (by decide)))

theorem fz1_49_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨8, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 8 (by decide)))

theorem fz1_49_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨9, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 9 (by decide)))

theorem fz1_49_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨10, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 10 (by decide)))

theorem fz1_49_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨11, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 11 (by decide)))

theorem fz1_49_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨13, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 13 (by decide)))

theorem fz1_49_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨14, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 14 (by decide)))

theorem fz1_49_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨15, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 15 (by decide)))

theorem fz1_49_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨16, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 16 (by decide)))

theorem fz1_49_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨17, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 17 (by decide)))

theorem fz1_49_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨18, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 18 (by decide)))

theorem fz1_49_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨19, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 19 (by decide)))

theorem fz1_49_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨20, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 20 (by decide)))

theorem fz1_49_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨21, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 21 (by decide)))

theorem fz1_49_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨22, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 22 (by decide)))

theorem fz1_49_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨23, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 23 (by decide)))

theorem fz1_49_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨24, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 24 (by decide)))

theorem fz1_49_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨25, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 25 (by decide)))

theorem fz1_49_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨26, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 26 (by decide)))

theorem fz1_49_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨27, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 27 (by decide)))

theorem fz1_49_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨28, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 28 (by decide)))

theorem fz1_49_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨29, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 29 (by decide)))

theorem fz1_49_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨30, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 30 (by decide)))

theorem fz1_49_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨31, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 31 (by decide)))

theorem fz1_49_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨32, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 32 (by decide)))

theorem fz1_49_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨33, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 33 (by decide)))

theorem fz1_49_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨34, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 34 (by decide)))

theorem fz1_49_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨35, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 35 (by decide)))

theorem fz1_49_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨36, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 36 (by decide)))

theorem fz1_49_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨37, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 37 (by decide)))

theorem fz1_49_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨38, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 38 (by decide)))

theorem fz1_49_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨39, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 39 (by decide)))

theorem fz1_49_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨40, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 40 (by decide)))

theorem fz1_49_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨41, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 41 (by decide)))

theorem fz1_49_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨42, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 42 (by decide)))

theorem fz1_49_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨43, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 43 (by decide)))

theorem fz1_49_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨44, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 44 (by decide)))

theorem fz1_49_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨45, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 45 (by decide)))

theorem fz1_49_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨46, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 46 (by decide)))

theorem fz1_49_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨47, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 47 (by decide)))

theorem fz1_49_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨48, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 48 (by decide)))

theorem fz1_49_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨50, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 50 (by decide)))

theorem fz1_49_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨51, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 51 (by decide)))

theorem fz1_49_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨52, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 52 (by decide)))

theorem fz1_49_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨53, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 53 (by decide)))

theorem fz1_49_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK49)) = 0 :=
  repsFixedCard rK49 ⟨54, by decide⟩ R49 hpxR49 hcardq49
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_49) 54 (by decide)))

theorem fixz2_49 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK49) (retConj 2 (Q2.R49_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_49_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨1, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 1 (by decide)))

theorem fz2_49_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨2, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 2 (by decide)))

theorem fz2_49_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨3, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 3 (by decide)))

theorem fz2_49_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨4, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 4 (by decide)))

theorem fz2_49_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨5, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 5 (by decide)))

theorem fz2_49_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨6, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 6 (by decide)))

theorem fz2_49_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨7, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 7 (by decide)))

theorem fz2_49_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨8, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 8 (by decide)))

theorem fz2_49_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨9, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 9 (by decide)))

theorem fz2_49_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨10, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 10 (by decide)))

theorem fz2_49_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨11, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 11 (by decide)))

theorem fz2_49_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨13, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 13 (by decide)))

theorem fz2_49_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨14, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 14 (by decide)))

theorem fz2_49_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨15, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 15 (by decide)))

theorem fz2_49_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨16, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 16 (by decide)))

theorem fz2_49_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨17, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 17 (by decide)))

theorem fz2_49_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨18, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 18 (by decide)))

theorem fz2_49_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨19, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 19 (by decide)))

theorem fz2_49_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨20, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 20 (by decide)))

theorem fz2_49_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨21, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 21 (by decide)))

theorem fz2_49_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨22, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 22 (by decide)))

theorem fz2_49_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨23, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 23 (by decide)))

theorem fz2_49_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨24, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 24 (by decide)))

theorem fz2_49_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨25, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 25 (by decide)))

theorem fz2_49_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨26, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 26 (by decide)))

theorem fz2_49_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨27, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 27 (by decide)))

theorem fz2_49_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨28, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 28 (by decide)))

theorem fz2_49_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨29, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 29 (by decide)))

theorem fz2_49_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨30, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 30 (by decide)))

theorem fz2_49_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨31, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 31 (by decide)))

theorem fz2_49_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨32, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 32 (by decide)))

theorem fz2_49_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨33, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 33 (by decide)))

theorem fz2_49_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨34, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 34 (by decide)))

theorem fz2_49_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨35, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 35 (by decide)))

theorem fz2_49_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨36, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 36 (by decide)))

theorem fz2_49_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨37, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 37 (by decide)))

theorem fz2_49_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨38, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 38 (by decide)))

theorem fz2_49_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨39, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 39 (by decide)))

theorem fz2_49_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨40, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 40 (by decide)))

theorem fz2_49_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨41, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 41 (by decide)))

theorem fz2_49_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨42, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 42 (by decide)))

theorem fz2_49_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨43, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 43 (by decide)))

theorem fz2_49_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨44, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 44 (by decide)))

theorem fz2_49_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨45, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 45 (by decide)))

theorem fz2_49_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨46, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 46 (by decide)))

theorem fz2_49_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨47, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 47 (by decide)))

theorem fz2_49_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨48, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 48 (by decide)))

theorem fz2_49_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨50, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 50 (by decide)))

theorem fz2_49_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨51, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 51 (by decide)))

theorem fz2_49_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨52, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 52 (by decide)))

theorem fz2_49_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨53, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 53 (by decide)))

theorem fz2_49_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK49)) = 0 :=
  Q2.repsFixedCard2 rK49 ⟨54, by decide⟩ Q2.R49_2 Q2.hpxR49_2 Q2.hcardq49_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_49) 54 (by decide)))

end LeanDring.P5Presentation
