/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C023

/-!
# Species-table cells, off-support emptiness certificates, chunk 34

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

theorem fixz1_35 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK35) (retConj 1 (R35 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_35_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨1, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 1 (by decide)))

theorem fz1_35_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨2, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 2 (by decide)))

theorem fz1_35_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨3, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 3 (by decide)))

theorem fz1_35_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨4, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 4 (by decide)))

theorem fz1_35_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨5, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 5 (by decide)))

theorem fz1_35_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨6, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 6 (by decide)))

theorem fz1_35_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨7, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 7 (by decide)))

theorem fz1_35_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨8, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 8 (by decide)))

theorem fz1_35_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨9, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 9 (by decide)))

theorem fz1_35_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨10, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 10 (by decide)))

theorem fz1_35_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨11, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 11 (by decide)))

theorem fz1_35_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨13, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 13 (by decide)))

theorem fz1_35_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨14, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 14 (by decide)))

theorem fz1_35_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨15, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 15 (by decide)))

theorem fz1_35_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨16, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 16 (by decide)))

theorem fz1_35_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨17, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 17 (by decide)))

theorem fz1_35_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨18, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 18 (by decide)))

theorem fz1_35_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨19, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 19 (by decide)))

theorem fz1_35_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨20, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 20 (by decide)))

theorem fz1_35_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨21, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 21 (by decide)))

theorem fz1_35_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨22, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 22 (by decide)))

theorem fz1_35_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨23, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 23 (by decide)))

theorem fz1_35_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨24, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 24 (by decide)))

theorem fz1_35_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨25, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 25 (by decide)))

theorem fz1_35_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨26, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 26 (by decide)))

theorem fz1_35_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨27, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 27 (by decide)))

theorem fz1_35_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨28, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 28 (by decide)))

theorem fz1_35_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨29, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 29 (by decide)))

theorem fz1_35_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨30, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 30 (by decide)))

theorem fz1_35_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨31, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 31 (by decide)))

theorem fz1_35_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨32, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 32 (by decide)))

theorem fz1_35_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨33, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 33 (by decide)))

theorem fz1_35_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨34, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 34 (by decide)))

theorem fz1_35_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨36, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 36 (by decide)))

theorem fz1_35_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨37, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 37 (by decide)))

theorem fz1_35_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨38, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 38 (by decide)))

theorem fz1_35_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨39, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 39 (by decide)))

theorem fz1_35_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨40, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 40 (by decide)))

theorem fz1_35_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨41, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 41 (by decide)))

theorem fz1_35_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨42, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 42 (by decide)))

theorem fz1_35_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨43, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 43 (by decide)))

theorem fz1_35_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨44, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 44 (by decide)))

theorem fz1_35_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨45, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 45 (by decide)))

theorem fz1_35_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨46, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 46 (by decide)))

theorem fz1_35_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨47, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 47 (by decide)))

theorem fz1_35_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨48, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 48 (by decide)))

theorem fz1_35_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨49, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 49 (by decide)))

theorem fz1_35_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨50, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 50 (by decide)))

theorem fz1_35_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨51, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 51 (by decide)))

theorem fz1_35_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨52, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 52 (by decide)))

theorem fz1_35_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨53, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 53 (by decide)))

theorem fz1_35_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK35)) = 0 :=
  repsFixedCard rK35 ⟨54, by decide⟩ R35 hpxR35 hcardq35
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_35) 54 (by decide)))

theorem fixz2_35 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK35) (retConj 2 (Q2.R35_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_35_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨1, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 1 (by decide)))

theorem fz2_35_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨2, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 2 (by decide)))

theorem fz2_35_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨3, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 3 (by decide)))

theorem fz2_35_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨4, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 4 (by decide)))

theorem fz2_35_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨5, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 5 (by decide)))

theorem fz2_35_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨6, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 6 (by decide)))

theorem fz2_35_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨7, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 7 (by decide)))

theorem fz2_35_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨8, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 8 (by decide)))

theorem fz2_35_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨9, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 9 (by decide)))

theorem fz2_35_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨10, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 10 (by decide)))

theorem fz2_35_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨11, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 11 (by decide)))

theorem fz2_35_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨13, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 13 (by decide)))

theorem fz2_35_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨14, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 14 (by decide)))

theorem fz2_35_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨15, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 15 (by decide)))

theorem fz2_35_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨16, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 16 (by decide)))

theorem fz2_35_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨17, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 17 (by decide)))

theorem fz2_35_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨18, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 18 (by decide)))

theorem fz2_35_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨19, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 19 (by decide)))

theorem fz2_35_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨20, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 20 (by decide)))

theorem fz2_35_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨21, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 21 (by decide)))

theorem fz2_35_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨22, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 22 (by decide)))

theorem fz2_35_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨23, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 23 (by decide)))

theorem fz2_35_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨24, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 24 (by decide)))

theorem fz2_35_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨25, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 25 (by decide)))

theorem fz2_35_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨26, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 26 (by decide)))

theorem fz2_35_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨27, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 27 (by decide)))

theorem fz2_35_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨28, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 28 (by decide)))

theorem fz2_35_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨29, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 29 (by decide)))

theorem fz2_35_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨30, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 30 (by decide)))

theorem fz2_35_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨31, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 31 (by decide)))

theorem fz2_35_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨32, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 32 (by decide)))

theorem fz2_35_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨33, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 33 (by decide)))

theorem fz2_35_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨34, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 34 (by decide)))

theorem fz2_35_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨36, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 36 (by decide)))

theorem fz2_35_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨37, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 37 (by decide)))

theorem fz2_35_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨38, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 38 (by decide)))

theorem fz2_35_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨39, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 39 (by decide)))

theorem fz2_35_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨40, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 40 (by decide)))

theorem fz2_35_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨41, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 41 (by decide)))

theorem fz2_35_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨42, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 42 (by decide)))

theorem fz2_35_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨43, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 43 (by decide)))

theorem fz2_35_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨44, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 44 (by decide)))

theorem fz2_35_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨45, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 45 (by decide)))

theorem fz2_35_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨46, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 46 (by decide)))

theorem fz2_35_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨47, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 47 (by decide)))

theorem fz2_35_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨48, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 48 (by decide)))

theorem fz2_35_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨49, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 49 (by decide)))

theorem fz2_35_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨50, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 50 (by decide)))

theorem fz2_35_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨51, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 51 (by decide)))

theorem fz2_35_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨52, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 52 (by decide)))

theorem fz2_35_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨53, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 53 (by decide)))

theorem fz2_35_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK35)) = 0 :=
  Q2.repsFixedCard2 rK35 ⟨54, by decide⟩ Q2.R35_2 Q2.hpxR35_2 Q2.hcardq35_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_35) 54 (by decide)))

end LeanDring.P5Presentation
