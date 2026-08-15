/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C006

/-!
# Species-table cells, off-support emptiness certificates, chunk 17

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

theorem fixz1_18 : ([1, 6, 7, 8, 10, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK18) (retConj 1 (R18 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_18_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨1, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 1 (by decide)))

theorem fz1_18_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨6, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 6 (by decide)))

theorem fz1_18_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨7, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 7 (by decide)))

theorem fz1_18_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨8, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 8 (by decide)))

theorem fz1_18_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨10, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 10 (by decide)))

theorem fz1_18_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨12, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 12 (by decide)))

theorem fz1_18_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨13, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 13 (by decide)))

theorem fz1_18_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨14, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 14 (by decide)))

theorem fz1_18_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨15, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 15 (by decide)))

theorem fz1_18_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨16, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 16 (by decide)))

theorem fz1_18_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨17, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 17 (by decide)))

theorem fz1_18_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨19, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 19 (by decide)))

theorem fz1_18_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨20, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 20 (by decide)))

theorem fz1_18_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨21, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 21 (by decide)))

theorem fz1_18_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨22, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 22 (by decide)))

theorem fz1_18_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨23, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 23 (by decide)))

theorem fz1_18_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨24, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 24 (by decide)))

theorem fz1_18_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨25, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 25 (by decide)))

theorem fz1_18_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨26, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 26 (by decide)))

theorem fz1_18_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨27, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 27 (by decide)))

theorem fz1_18_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨28, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 28 (by decide)))

theorem fz1_18_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨29, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 29 (by decide)))

theorem fz1_18_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨30, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 30 (by decide)))

theorem fz1_18_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨31, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 31 (by decide)))

theorem fz1_18_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨32, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 32 (by decide)))

theorem fz1_18_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨33, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 33 (by decide)))

theorem fz1_18_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨34, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 34 (by decide)))

theorem fz1_18_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨35, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 35 (by decide)))

theorem fz1_18_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨36, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 36 (by decide)))

theorem fz1_18_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨37, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 37 (by decide)))

theorem fz1_18_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨38, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 38 (by decide)))

theorem fz1_18_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨39, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 39 (by decide)))

theorem fz1_18_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨40, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 40 (by decide)))

theorem fz1_18_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨41, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 41 (by decide)))

theorem fz1_18_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨42, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 42 (by decide)))

theorem fz1_18_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨43, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 43 (by decide)))

theorem fz1_18_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨44, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 44 (by decide)))

theorem fz1_18_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨45, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 45 (by decide)))

theorem fz1_18_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨46, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 46 (by decide)))

theorem fz1_18_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨47, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 47 (by decide)))

theorem fz1_18_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨48, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 48 (by decide)))

theorem fz1_18_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨49, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 49 (by decide)))

theorem fz1_18_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨50, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 50 (by decide)))

theorem fz1_18_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨51, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 51 (by decide)))

theorem fz1_18_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨52, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 52 (by decide)))

theorem fz1_18_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨53, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 53 (by decide)))

theorem fz1_18_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK18)) = 0 :=
  repsFixedCard rK18 ⟨54, by decide⟩ R18 hpxR18 hcardq18
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_18) 54 (by decide)))

theorem fixz2_18 : ([1, 6, 7, 8, 10, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK18) (retConj 2 (Q2.R18_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_18_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨1, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 1 (by decide)))

theorem fz2_18_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨6, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 6 (by decide)))

theorem fz2_18_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨7, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 7 (by decide)))

theorem fz2_18_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨8, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 8 (by decide)))

theorem fz2_18_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨10, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 10 (by decide)))

theorem fz2_18_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨12, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 12 (by decide)))

theorem fz2_18_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨13, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 13 (by decide)))

theorem fz2_18_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨14, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 14 (by decide)))

theorem fz2_18_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨15, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 15 (by decide)))

theorem fz2_18_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨16, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 16 (by decide)))

theorem fz2_18_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨17, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 17 (by decide)))

theorem fz2_18_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨19, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 19 (by decide)))

theorem fz2_18_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨20, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 20 (by decide)))

theorem fz2_18_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨21, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 21 (by decide)))

theorem fz2_18_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨22, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 22 (by decide)))

theorem fz2_18_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨23, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 23 (by decide)))

theorem fz2_18_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨24, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 24 (by decide)))

theorem fz2_18_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨25, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 25 (by decide)))

theorem fz2_18_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨26, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 26 (by decide)))

theorem fz2_18_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨27, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 27 (by decide)))

theorem fz2_18_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨28, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 28 (by decide)))

theorem fz2_18_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨29, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 29 (by decide)))

theorem fz2_18_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨30, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 30 (by decide)))

theorem fz2_18_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨31, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 31 (by decide)))

theorem fz2_18_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨32, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 32 (by decide)))

theorem fz2_18_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨33, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 33 (by decide)))

theorem fz2_18_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨34, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 34 (by decide)))

theorem fz2_18_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨35, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 35 (by decide)))

theorem fz2_18_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨36, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 36 (by decide)))

theorem fz2_18_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨37, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 37 (by decide)))

theorem fz2_18_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨38, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 38 (by decide)))

theorem fz2_18_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨39, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 39 (by decide)))

theorem fz2_18_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨40, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 40 (by decide)))

theorem fz2_18_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨41, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 41 (by decide)))

theorem fz2_18_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨42, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 42 (by decide)))

theorem fz2_18_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨43, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 43 (by decide)))

theorem fz2_18_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨44, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 44 (by decide)))

theorem fz2_18_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨45, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 45 (by decide)))

theorem fz2_18_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨46, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 46 (by decide)))

theorem fz2_18_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨47, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 47 (by decide)))

theorem fz2_18_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨48, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 48 (by decide)))

theorem fz2_18_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨49, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 49 (by decide)))

theorem fz2_18_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨50, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 50 (by decide)))

theorem fz2_18_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨51, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 51 (by decide)))

theorem fz2_18_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨52, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 52 (by decide)))

theorem fz2_18_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨53, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 53 (by decide)))

theorem fz2_18_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK18)) = 0 :=
  Q2.repsFixedCard2 rK18 ⟨54, by decide⟩ Q2.R18_2 Q2.hpxR18_2 Q2.hcardq18_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_18) 54 (by decide)))

end LeanDring.P5Presentation
