/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C033

/-!
# Species-table cells, off-support emptiness certificates, chunk 44

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

theorem fixz1_45 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK45) (retConj 1 (R45 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_45_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨1, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 1 (by decide)))

theorem fz1_45_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨2, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 2 (by decide)))

theorem fz1_45_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨3, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 3 (by decide)))

theorem fz1_45_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨4, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 4 (by decide)))

theorem fz1_45_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨5, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 5 (by decide)))

theorem fz1_45_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨6, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 6 (by decide)))

theorem fz1_45_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨7, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 7 (by decide)))

theorem fz1_45_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨8, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 8 (by decide)))

theorem fz1_45_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨9, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 9 (by decide)))

theorem fz1_45_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨10, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 10 (by decide)))

theorem fz1_45_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨11, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 11 (by decide)))

theorem fz1_45_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨13, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 13 (by decide)))

theorem fz1_45_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨14, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 14 (by decide)))

theorem fz1_45_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨15, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 15 (by decide)))

theorem fz1_45_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨16, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 16 (by decide)))

theorem fz1_45_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨17, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 17 (by decide)))

theorem fz1_45_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨18, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 18 (by decide)))

theorem fz1_45_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨19, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 19 (by decide)))

theorem fz1_45_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨20, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 20 (by decide)))

theorem fz1_45_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨21, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 21 (by decide)))

theorem fz1_45_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨22, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 22 (by decide)))

theorem fz1_45_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨23, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 23 (by decide)))

theorem fz1_45_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨24, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 24 (by decide)))

theorem fz1_45_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨25, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 25 (by decide)))

theorem fz1_45_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨26, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 26 (by decide)))

theorem fz1_45_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨27, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 27 (by decide)))

theorem fz1_45_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨28, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 28 (by decide)))

theorem fz1_45_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨29, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 29 (by decide)))

theorem fz1_45_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨30, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 30 (by decide)))

theorem fz1_45_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨31, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 31 (by decide)))

theorem fz1_45_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨32, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 32 (by decide)))

theorem fz1_45_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨33, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 33 (by decide)))

theorem fz1_45_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨34, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 34 (by decide)))

theorem fz1_45_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨35, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 35 (by decide)))

theorem fz1_45_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨36, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 36 (by decide)))

theorem fz1_45_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨37, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 37 (by decide)))

theorem fz1_45_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨38, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 38 (by decide)))

theorem fz1_45_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨39, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 39 (by decide)))

theorem fz1_45_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨40, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 40 (by decide)))

theorem fz1_45_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨41, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 41 (by decide)))

theorem fz1_45_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨42, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 42 (by decide)))

theorem fz1_45_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨43, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 43 (by decide)))

theorem fz1_45_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨44, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 44 (by decide)))

theorem fz1_45_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨46, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 46 (by decide)))

theorem fz1_45_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨47, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 47 (by decide)))

theorem fz1_45_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨48, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 48 (by decide)))

theorem fz1_45_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨49, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 49 (by decide)))

theorem fz1_45_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨50, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 50 (by decide)))

theorem fz1_45_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨51, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 51 (by decide)))

theorem fz1_45_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨52, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 52 (by decide)))

theorem fz1_45_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨53, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 53 (by decide)))

theorem fz1_45_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK45)) = 0 :=
  repsFixedCard rK45 ⟨54, by decide⟩ R45 hpxR45 hcardq45
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_45) 54 (by decide)))

theorem fixz2_45 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK45) (retConj 2 (Q2.R45_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_45_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨1, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 1 (by decide)))

theorem fz2_45_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨2, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 2 (by decide)))

theorem fz2_45_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨3, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 3 (by decide)))

theorem fz2_45_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨4, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 4 (by decide)))

theorem fz2_45_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨5, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 5 (by decide)))

theorem fz2_45_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨6, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 6 (by decide)))

theorem fz2_45_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨7, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 7 (by decide)))

theorem fz2_45_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨8, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 8 (by decide)))

theorem fz2_45_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨9, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 9 (by decide)))

theorem fz2_45_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨10, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 10 (by decide)))

theorem fz2_45_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨11, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 11 (by decide)))

theorem fz2_45_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨13, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 13 (by decide)))

theorem fz2_45_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨14, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 14 (by decide)))

theorem fz2_45_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨15, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 15 (by decide)))

theorem fz2_45_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨16, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 16 (by decide)))

theorem fz2_45_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨17, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 17 (by decide)))

theorem fz2_45_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨18, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 18 (by decide)))

theorem fz2_45_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨19, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 19 (by decide)))

theorem fz2_45_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨20, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 20 (by decide)))

theorem fz2_45_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨21, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 21 (by decide)))

theorem fz2_45_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨22, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 22 (by decide)))

theorem fz2_45_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨23, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 23 (by decide)))

theorem fz2_45_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨24, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 24 (by decide)))

theorem fz2_45_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨25, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 25 (by decide)))

theorem fz2_45_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨26, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 26 (by decide)))

theorem fz2_45_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨27, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 27 (by decide)))

theorem fz2_45_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨28, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 28 (by decide)))

theorem fz2_45_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨29, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 29 (by decide)))

theorem fz2_45_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨30, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 30 (by decide)))

theorem fz2_45_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨31, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 31 (by decide)))

theorem fz2_45_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨32, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 32 (by decide)))

theorem fz2_45_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨33, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 33 (by decide)))

theorem fz2_45_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨34, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 34 (by decide)))

theorem fz2_45_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨35, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 35 (by decide)))

theorem fz2_45_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨36, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 36 (by decide)))

theorem fz2_45_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨37, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 37 (by decide)))

theorem fz2_45_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨38, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 38 (by decide)))

theorem fz2_45_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨39, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 39 (by decide)))

theorem fz2_45_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨40, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 40 (by decide)))

theorem fz2_45_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨41, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 41 (by decide)))

theorem fz2_45_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨42, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 42 (by decide)))

theorem fz2_45_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨43, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 43 (by decide)))

theorem fz2_45_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨44, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 44 (by decide)))

theorem fz2_45_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨46, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 46 (by decide)))

theorem fz2_45_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨47, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 47 (by decide)))

theorem fz2_45_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨48, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 48 (by decide)))

theorem fz2_45_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨49, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 49 (by decide)))

theorem fz2_45_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨50, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 50 (by decide)))

theorem fz2_45_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨51, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 51 (by decide)))

theorem fz2_45_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨52, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 52 (by decide)))

theorem fz2_45_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨53, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 53 (by decide)))

theorem fz2_45_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK45)) = 0 :=
  Q2.repsFixedCard2 rK45 ⟨54, by decide⟩ Q2.R45_2 Q2.hpxR45_2 Q2.hcardq45_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_45) 54 (by decide)))

end LeanDring.P5Presentation
