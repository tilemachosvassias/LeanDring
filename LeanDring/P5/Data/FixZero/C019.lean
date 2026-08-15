/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C007

/-!
# Species-table cells, off-support emptiness certificates, chunk 18

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

theorem fixz1_19 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK19) (retConj 1 (R19 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_19_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨2, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 2 (by decide)))

theorem fz1_19_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨3, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 3 (by decide)))

theorem fz1_19_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨4, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 4 (by decide)))

theorem fz1_19_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨5, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 5 (by decide)))

theorem fz1_19_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨6, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 6 (by decide)))

theorem fz1_19_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨7, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 7 (by decide)))

theorem fz1_19_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨8, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 8 (by decide)))

theorem fz1_19_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨9, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 9 (by decide)))

theorem fz1_19_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨10, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 10 (by decide)))

theorem fz1_19_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨11, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 11 (by decide)))

theorem fz1_19_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨13, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 13 (by decide)))

theorem fz1_19_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨14, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 14 (by decide)))

theorem fz1_19_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨15, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 15 (by decide)))

theorem fz1_19_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨16, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 16 (by decide)))

theorem fz1_19_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨17, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 17 (by decide)))

theorem fz1_19_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨18, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 18 (by decide)))

theorem fz1_19_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨20, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 20 (by decide)))

theorem fz1_19_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨21, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 21 (by decide)))

theorem fz1_19_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨22, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 22 (by decide)))

theorem fz1_19_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨23, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 23 (by decide)))

theorem fz1_19_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨24, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 24 (by decide)))

theorem fz1_19_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨25, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 25 (by decide)))

theorem fz1_19_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨26, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 26 (by decide)))

theorem fz1_19_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨27, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 27 (by decide)))

theorem fz1_19_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨28, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 28 (by decide)))

theorem fz1_19_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨29, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 29 (by decide)))

theorem fz1_19_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨30, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 30 (by decide)))

theorem fz1_19_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨31, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 31 (by decide)))

theorem fz1_19_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨32, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 32 (by decide)))

theorem fz1_19_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨33, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 33 (by decide)))

theorem fz1_19_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨34, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 34 (by decide)))

theorem fz1_19_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨35, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 35 (by decide)))

theorem fz1_19_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨36, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 36 (by decide)))

theorem fz1_19_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨37, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 37 (by decide)))

theorem fz1_19_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨38, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 38 (by decide)))

theorem fz1_19_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨39, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 39 (by decide)))

theorem fz1_19_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨40, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 40 (by decide)))

theorem fz1_19_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨41, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 41 (by decide)))

theorem fz1_19_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨42, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 42 (by decide)))

theorem fz1_19_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨43, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 43 (by decide)))

theorem fz1_19_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨44, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 44 (by decide)))

theorem fz1_19_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨45, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 45 (by decide)))

theorem fz1_19_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨46, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 46 (by decide)))

theorem fz1_19_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨47, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 47 (by decide)))

theorem fz1_19_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨48, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 48 (by decide)))

theorem fz1_19_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨49, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 49 (by decide)))

theorem fz1_19_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨50, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 50 (by decide)))

theorem fz1_19_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨51, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 51 (by decide)))

theorem fz1_19_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨52, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 52 (by decide)))

theorem fz1_19_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨53, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 53 (by decide)))

theorem fz1_19_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK19)) = 0 :=
  repsFixedCard rK19 ⟨54, by decide⟩ R19 hpxR19 hcardq19
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_19) 54 (by decide)))

theorem fixz2_19 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK19) (retConj 2 (Q2.R19_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_19_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨2, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 2 (by decide)))

theorem fz2_19_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨3, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 3 (by decide)))

theorem fz2_19_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨4, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 4 (by decide)))

theorem fz2_19_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨5, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 5 (by decide)))

theorem fz2_19_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨6, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 6 (by decide)))

theorem fz2_19_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨7, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 7 (by decide)))

theorem fz2_19_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨8, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 8 (by decide)))

theorem fz2_19_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨9, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 9 (by decide)))

theorem fz2_19_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨10, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 10 (by decide)))

theorem fz2_19_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨11, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 11 (by decide)))

theorem fz2_19_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨13, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 13 (by decide)))

theorem fz2_19_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨14, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 14 (by decide)))

theorem fz2_19_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨15, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 15 (by decide)))

theorem fz2_19_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨16, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 16 (by decide)))

theorem fz2_19_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨17, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 17 (by decide)))

theorem fz2_19_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨18, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 18 (by decide)))

theorem fz2_19_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨20, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 20 (by decide)))

theorem fz2_19_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨21, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 21 (by decide)))

theorem fz2_19_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨22, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 22 (by decide)))

theorem fz2_19_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨23, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 23 (by decide)))

theorem fz2_19_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨24, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 24 (by decide)))

theorem fz2_19_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨25, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 25 (by decide)))

theorem fz2_19_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨26, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 26 (by decide)))

theorem fz2_19_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨27, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 27 (by decide)))

theorem fz2_19_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨28, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 28 (by decide)))

theorem fz2_19_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨29, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 29 (by decide)))

theorem fz2_19_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨30, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 30 (by decide)))

theorem fz2_19_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨31, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 31 (by decide)))

theorem fz2_19_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨32, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 32 (by decide)))

theorem fz2_19_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨33, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 33 (by decide)))

theorem fz2_19_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨34, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 34 (by decide)))

theorem fz2_19_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨35, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 35 (by decide)))

theorem fz2_19_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨36, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 36 (by decide)))

theorem fz2_19_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨37, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 37 (by decide)))

theorem fz2_19_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨38, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 38 (by decide)))

theorem fz2_19_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨39, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 39 (by decide)))

theorem fz2_19_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨40, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 40 (by decide)))

theorem fz2_19_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨41, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 41 (by decide)))

theorem fz2_19_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨42, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 42 (by decide)))

theorem fz2_19_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨43, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 43 (by decide)))

theorem fz2_19_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨44, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 44 (by decide)))

theorem fz2_19_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨45, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 45 (by decide)))

theorem fz2_19_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨46, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 46 (by decide)))

theorem fz2_19_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨47, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 47 (by decide)))

theorem fz2_19_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨48, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 48 (by decide)))

theorem fz2_19_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨49, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 49 (by decide)))

theorem fz2_19_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨50, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 50 (by decide)))

theorem fz2_19_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨51, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 51 (by decide)))

theorem fz2_19_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨52, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 52 (by decide)))

theorem fz2_19_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨53, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 53 (by decide)))

theorem fz2_19_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK19)) = 0 :=
  Q2.repsFixedCard2 rK19 ⟨54, by decide⟩ Q2.R19_2 Q2.hpxR19_2 Q2.hcardq19_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_19) 54 (by decide)))

end LeanDring.P5Presentation
