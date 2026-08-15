/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C014

/-!
# Species-table cells, off-support emptiness certificates, chunk 25

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

theorem fixz1_26 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK26) (retConj 1 (R26 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_26_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨1, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 1 (by decide)))

theorem fz1_26_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨2, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 2 (by decide)))

theorem fz1_26_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨3, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 3 (by decide)))

theorem fz1_26_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨4, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 4 (by decide)))

theorem fz1_26_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨5, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 5 (by decide)))

theorem fz1_26_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨6, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 6 (by decide)))

theorem fz1_26_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨7, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 7 (by decide)))

theorem fz1_26_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨9, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 9 (by decide)))

theorem fz1_26_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨10, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 10 (by decide)))

theorem fz1_26_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨11, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 11 (by decide)))

theorem fz1_26_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨13, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 13 (by decide)))

theorem fz1_26_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨14, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 14 (by decide)))

theorem fz1_26_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨15, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 15 (by decide)))

theorem fz1_26_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨16, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 16 (by decide)))

theorem fz1_26_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨17, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 17 (by decide)))

theorem fz1_26_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨18, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 18 (by decide)))

theorem fz1_26_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨19, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 19 (by decide)))

theorem fz1_26_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨20, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 20 (by decide)))

theorem fz1_26_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨21, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 21 (by decide)))

theorem fz1_26_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨22, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 22 (by decide)))

theorem fz1_26_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨23, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 23 (by decide)))

theorem fz1_26_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨24, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 24 (by decide)))

theorem fz1_26_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨25, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 25 (by decide)))

theorem fz1_26_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨27, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 27 (by decide)))

theorem fz1_26_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨28, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 28 (by decide)))

theorem fz1_26_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨29, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 29 (by decide)))

theorem fz1_26_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨30, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 30 (by decide)))

theorem fz1_26_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨31, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 31 (by decide)))

theorem fz1_26_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨32, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 32 (by decide)))

theorem fz1_26_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨33, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 33 (by decide)))

theorem fz1_26_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨34, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 34 (by decide)))

theorem fz1_26_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨35, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 35 (by decide)))

theorem fz1_26_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨36, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 36 (by decide)))

theorem fz1_26_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨37, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 37 (by decide)))

theorem fz1_26_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨38, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 38 (by decide)))

theorem fz1_26_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨39, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 39 (by decide)))

theorem fz1_26_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨40, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 40 (by decide)))

theorem fz1_26_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨41, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 41 (by decide)))

theorem fz1_26_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨42, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 42 (by decide)))

theorem fz1_26_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨43, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 43 (by decide)))

theorem fz1_26_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨44, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 44 (by decide)))

theorem fz1_26_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨45, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 45 (by decide)))

theorem fz1_26_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨46, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 46 (by decide)))

theorem fz1_26_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨47, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 47 (by decide)))

theorem fz1_26_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨48, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 48 (by decide)))

theorem fz1_26_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨49, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 49 (by decide)))

theorem fz1_26_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨50, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 50 (by decide)))

theorem fz1_26_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨51, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 51 (by decide)))

theorem fz1_26_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨52, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 52 (by decide)))

theorem fz1_26_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨53, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 53 (by decide)))

theorem fz1_26_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK26)) = 0 :=
  repsFixedCard rK26 ⟨54, by decide⟩ R26 hpxR26 hcardq26
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_26) 54 (by decide)))

theorem fixz2_26 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK26) (retConj 2 (Q2.R26_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_26_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨1, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 1 (by decide)))

theorem fz2_26_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨2, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 2 (by decide)))

theorem fz2_26_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨3, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 3 (by decide)))

theorem fz2_26_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨4, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 4 (by decide)))

theorem fz2_26_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨5, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 5 (by decide)))

theorem fz2_26_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨6, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 6 (by decide)))

theorem fz2_26_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨7, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 7 (by decide)))

theorem fz2_26_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨9, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 9 (by decide)))

theorem fz2_26_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨10, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 10 (by decide)))

theorem fz2_26_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨11, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 11 (by decide)))

theorem fz2_26_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨13, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 13 (by decide)))

theorem fz2_26_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨14, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 14 (by decide)))

theorem fz2_26_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨15, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 15 (by decide)))

theorem fz2_26_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨16, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 16 (by decide)))

theorem fz2_26_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨17, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 17 (by decide)))

theorem fz2_26_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨18, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 18 (by decide)))

theorem fz2_26_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨19, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 19 (by decide)))

theorem fz2_26_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨20, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 20 (by decide)))

theorem fz2_26_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨21, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 21 (by decide)))

theorem fz2_26_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨22, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 22 (by decide)))

theorem fz2_26_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨23, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 23 (by decide)))

theorem fz2_26_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨24, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 24 (by decide)))

theorem fz2_26_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨25, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 25 (by decide)))

theorem fz2_26_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨27, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 27 (by decide)))

theorem fz2_26_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨28, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 28 (by decide)))

theorem fz2_26_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨29, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 29 (by decide)))

theorem fz2_26_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨30, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 30 (by decide)))

theorem fz2_26_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨31, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 31 (by decide)))

theorem fz2_26_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨32, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 32 (by decide)))

theorem fz2_26_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨33, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 33 (by decide)))

theorem fz2_26_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨34, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 34 (by decide)))

theorem fz2_26_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨35, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 35 (by decide)))

theorem fz2_26_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨36, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 36 (by decide)))

theorem fz2_26_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨37, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 37 (by decide)))

theorem fz2_26_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨38, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 38 (by decide)))

theorem fz2_26_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨39, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 39 (by decide)))

theorem fz2_26_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨40, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 40 (by decide)))

theorem fz2_26_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨41, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 41 (by decide)))

theorem fz2_26_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨42, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 42 (by decide)))

theorem fz2_26_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨43, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 43 (by decide)))

theorem fz2_26_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨44, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 44 (by decide)))

theorem fz2_26_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨45, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 45 (by decide)))

theorem fz2_26_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨46, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 46 (by decide)))

theorem fz2_26_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨47, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 47 (by decide)))

theorem fz2_26_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨48, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 48 (by decide)))

theorem fz2_26_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨49, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 49 (by decide)))

theorem fz2_26_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨50, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 50 (by decide)))

theorem fz2_26_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨51, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 51 (by decide)))

theorem fz2_26_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨52, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 52 (by decide)))

theorem fz2_26_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨53, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 53 (by decide)))

theorem fz2_26_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK26)) = 0 :=
  Q2.repsFixedCard2 rK26 ⟨54, by decide⟩ Q2.R26_2 Q2.hpxR26_2 Q2.hcardq26_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_26) 54 (by decide)))

end LeanDring.P5Presentation
