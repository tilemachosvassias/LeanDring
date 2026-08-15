/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C009

/-!
# Species-table cells, off-support emptiness certificates, chunk 20

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

theorem fixz1_21 : ([1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK21) (retConj 1 (R21 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_21_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨1, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 1 (by decide)))

theorem fz1_21_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨2, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 2 (by decide)))

theorem fz1_21_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨4, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 4 (by decide)))

theorem fz1_21_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨5, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 5 (by decide)))

theorem fz1_21_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨6, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 6 (by decide)))

theorem fz1_21_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨7, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 7 (by decide)))

theorem fz1_21_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨8, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 8 (by decide)))

theorem fz1_21_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨9, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 9 (by decide)))

theorem fz1_21_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨10, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 10 (by decide)))

theorem fz1_21_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨11, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 11 (by decide)))

theorem fz1_21_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨13, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 13 (by decide)))

theorem fz1_21_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨14, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 14 (by decide)))

theorem fz1_21_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨15, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 15 (by decide)))

theorem fz1_21_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨16, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 16 (by decide)))

theorem fz1_21_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨17, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 17 (by decide)))

theorem fz1_21_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨18, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 18 (by decide)))

theorem fz1_21_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨19, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 19 (by decide)))

theorem fz1_21_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨20, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 20 (by decide)))

theorem fz1_21_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨22, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 22 (by decide)))

theorem fz1_21_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨23, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 23 (by decide)))

theorem fz1_21_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨24, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 24 (by decide)))

theorem fz1_21_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨25, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 25 (by decide)))

theorem fz1_21_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨26, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 26 (by decide)))

theorem fz1_21_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨27, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 27 (by decide)))

theorem fz1_21_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨28, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 28 (by decide)))

theorem fz1_21_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨29, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 29 (by decide)))

theorem fz1_21_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨30, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 30 (by decide)))

theorem fz1_21_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨31, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 31 (by decide)))

theorem fz1_21_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨32, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 32 (by decide)))

theorem fz1_21_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨33, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 33 (by decide)))

theorem fz1_21_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨34, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 34 (by decide)))

theorem fz1_21_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨35, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 35 (by decide)))

theorem fz1_21_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨36, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 36 (by decide)))

theorem fz1_21_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨37, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 37 (by decide)))

theorem fz1_21_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨38, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 38 (by decide)))

theorem fz1_21_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨39, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 39 (by decide)))

theorem fz1_21_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨40, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 40 (by decide)))

theorem fz1_21_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨41, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 41 (by decide)))

theorem fz1_21_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨42, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 42 (by decide)))

theorem fz1_21_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨43, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 43 (by decide)))

theorem fz1_21_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨44, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 44 (by decide)))

theorem fz1_21_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨45, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 45 (by decide)))

theorem fz1_21_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨46, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 46 (by decide)))

theorem fz1_21_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨47, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 47 (by decide)))

theorem fz1_21_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨48, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 48 (by decide)))

theorem fz1_21_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨49, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 49 (by decide)))

theorem fz1_21_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨50, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 50 (by decide)))

theorem fz1_21_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨51, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 51 (by decide)))

theorem fz1_21_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨52, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 52 (by decide)))

theorem fz1_21_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨53, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 53 (by decide)))

theorem fz1_21_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK21)) = 0 :=
  repsFixedCard rK21 ⟨54, by decide⟩ R21 hpxR21 hcardq21
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_21) 54 (by decide)))

theorem fixz2_21 : ([1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK21) (retConj 2 (Q2.R21_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_21_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨1, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 1 (by decide)))

theorem fz2_21_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨2, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 2 (by decide)))

theorem fz2_21_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨4, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 4 (by decide)))

theorem fz2_21_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨5, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 5 (by decide)))

theorem fz2_21_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨6, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 6 (by decide)))

theorem fz2_21_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨7, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 7 (by decide)))

theorem fz2_21_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨8, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 8 (by decide)))

theorem fz2_21_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨9, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 9 (by decide)))

theorem fz2_21_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨10, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 10 (by decide)))

theorem fz2_21_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨11, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 11 (by decide)))

theorem fz2_21_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨13, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 13 (by decide)))

theorem fz2_21_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨14, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 14 (by decide)))

theorem fz2_21_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨15, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 15 (by decide)))

theorem fz2_21_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨16, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 16 (by decide)))

theorem fz2_21_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨17, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 17 (by decide)))

theorem fz2_21_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨18, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 18 (by decide)))

theorem fz2_21_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨19, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 19 (by decide)))

theorem fz2_21_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨20, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 20 (by decide)))

theorem fz2_21_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨22, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 22 (by decide)))

theorem fz2_21_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨23, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 23 (by decide)))

theorem fz2_21_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨24, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 24 (by decide)))

theorem fz2_21_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨25, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 25 (by decide)))

theorem fz2_21_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨26, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 26 (by decide)))

theorem fz2_21_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨27, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 27 (by decide)))

theorem fz2_21_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨28, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 28 (by decide)))

theorem fz2_21_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨29, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 29 (by decide)))

theorem fz2_21_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨30, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 30 (by decide)))

theorem fz2_21_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨31, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 31 (by decide)))

theorem fz2_21_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨32, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 32 (by decide)))

theorem fz2_21_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨33, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 33 (by decide)))

theorem fz2_21_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨34, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 34 (by decide)))

theorem fz2_21_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨35, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 35 (by decide)))

theorem fz2_21_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨36, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 36 (by decide)))

theorem fz2_21_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨37, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 37 (by decide)))

theorem fz2_21_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨38, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 38 (by decide)))

theorem fz2_21_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨39, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 39 (by decide)))

theorem fz2_21_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨40, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 40 (by decide)))

theorem fz2_21_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨41, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 41 (by decide)))

theorem fz2_21_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨42, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 42 (by decide)))

theorem fz2_21_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨43, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 43 (by decide)))

theorem fz2_21_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨44, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 44 (by decide)))

theorem fz2_21_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨45, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 45 (by decide)))

theorem fz2_21_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨46, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 46 (by decide)))

theorem fz2_21_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨47, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 47 (by decide)))

theorem fz2_21_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨48, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 48 (by decide)))

theorem fz2_21_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨49, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 49 (by decide)))

theorem fz2_21_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨50, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 50 (by decide)))

theorem fz2_21_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨51, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 51 (by decide)))

theorem fz2_21_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨52, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 52 (by decide)))

theorem fz2_21_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨53, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 53 (by decide)))

theorem fz2_21_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK21)) = 0 :=
  Q2.repsFixedCard2 rK21 ⟨54, by decide⟩ Q2.R21_2 Q2.hpxR21_2 Q2.hcardq21_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_21) 54 (by decide)))

end LeanDring.P5Presentation
