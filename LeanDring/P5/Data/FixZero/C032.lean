/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C020

/-!
# Species-table cells, off-support emptiness certificates, chunk 31

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

theorem fixz1_32 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK32) (retConj 1 (R32 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_32_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨1, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 1 (by decide)))

theorem fz1_32_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨2, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 2 (by decide)))

theorem fz1_32_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨3, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 3 (by decide)))

theorem fz1_32_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨4, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 4 (by decide)))

theorem fz1_32_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨5, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 5 (by decide)))

theorem fz1_32_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨6, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 6 (by decide)))

theorem fz1_32_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨7, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 7 (by decide)))

theorem fz1_32_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨8, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 8 (by decide)))

theorem fz1_32_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨9, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 9 (by decide)))

theorem fz1_32_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨10, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 10 (by decide)))

theorem fz1_32_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨11, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 11 (by decide)))

theorem fz1_32_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨13, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 13 (by decide)))

theorem fz1_32_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨14, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 14 (by decide)))

theorem fz1_32_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨15, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 15 (by decide)))

theorem fz1_32_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨16, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 16 (by decide)))

theorem fz1_32_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨17, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 17 (by decide)))

theorem fz1_32_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨18, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 18 (by decide)))

theorem fz1_32_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨19, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 19 (by decide)))

theorem fz1_32_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨20, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 20 (by decide)))

theorem fz1_32_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨21, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 21 (by decide)))

theorem fz1_32_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨22, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 22 (by decide)))

theorem fz1_32_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨23, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 23 (by decide)))

theorem fz1_32_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨24, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 24 (by decide)))

theorem fz1_32_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨25, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 25 (by decide)))

theorem fz1_32_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨26, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 26 (by decide)))

theorem fz1_32_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨27, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 27 (by decide)))

theorem fz1_32_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨28, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 28 (by decide)))

theorem fz1_32_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨29, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 29 (by decide)))

theorem fz1_32_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨30, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 30 (by decide)))

theorem fz1_32_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨31, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 31 (by decide)))

theorem fz1_32_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨33, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 33 (by decide)))

theorem fz1_32_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨34, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 34 (by decide)))

theorem fz1_32_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨35, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 35 (by decide)))

theorem fz1_32_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨36, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 36 (by decide)))

theorem fz1_32_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨37, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 37 (by decide)))

theorem fz1_32_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨38, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 38 (by decide)))

theorem fz1_32_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨39, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 39 (by decide)))

theorem fz1_32_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨40, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 40 (by decide)))

theorem fz1_32_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨41, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 41 (by decide)))

theorem fz1_32_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨42, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 42 (by decide)))

theorem fz1_32_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨43, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 43 (by decide)))

theorem fz1_32_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨44, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 44 (by decide)))

theorem fz1_32_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨45, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 45 (by decide)))

theorem fz1_32_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨46, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 46 (by decide)))

theorem fz1_32_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨47, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 47 (by decide)))

theorem fz1_32_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨48, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 48 (by decide)))

theorem fz1_32_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨49, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 49 (by decide)))

theorem fz1_32_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨50, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 50 (by decide)))

theorem fz1_32_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨51, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 51 (by decide)))

theorem fz1_32_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨52, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 52 (by decide)))

theorem fz1_32_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨53, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 53 (by decide)))

theorem fz1_32_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK32)) = 0 :=
  repsFixedCard rK32 ⟨54, by decide⟩ R32 hpxR32 hcardq32
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_32) 54 (by decide)))

theorem fixz2_32 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK32) (retConj 2 (Q2.R32_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_32_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨1, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 1 (by decide)))

theorem fz2_32_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨2, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 2 (by decide)))

theorem fz2_32_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨3, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 3 (by decide)))

theorem fz2_32_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨4, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 4 (by decide)))

theorem fz2_32_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨5, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 5 (by decide)))

theorem fz2_32_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨6, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 6 (by decide)))

theorem fz2_32_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨7, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 7 (by decide)))

theorem fz2_32_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨8, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 8 (by decide)))

theorem fz2_32_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨9, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 9 (by decide)))

theorem fz2_32_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨10, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 10 (by decide)))

theorem fz2_32_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨11, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 11 (by decide)))

theorem fz2_32_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨13, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 13 (by decide)))

theorem fz2_32_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨14, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 14 (by decide)))

theorem fz2_32_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨15, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 15 (by decide)))

theorem fz2_32_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨16, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 16 (by decide)))

theorem fz2_32_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨17, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 17 (by decide)))

theorem fz2_32_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨18, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 18 (by decide)))

theorem fz2_32_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨19, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 19 (by decide)))

theorem fz2_32_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨20, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 20 (by decide)))

theorem fz2_32_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨21, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 21 (by decide)))

theorem fz2_32_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨22, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 22 (by decide)))

theorem fz2_32_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨23, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 23 (by decide)))

theorem fz2_32_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨24, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 24 (by decide)))

theorem fz2_32_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨25, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 25 (by decide)))

theorem fz2_32_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨26, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 26 (by decide)))

theorem fz2_32_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨27, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 27 (by decide)))

theorem fz2_32_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨28, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 28 (by decide)))

theorem fz2_32_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨29, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 29 (by decide)))

theorem fz2_32_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨30, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 30 (by decide)))

theorem fz2_32_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨31, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 31 (by decide)))

theorem fz2_32_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨33, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 33 (by decide)))

theorem fz2_32_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨34, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 34 (by decide)))

theorem fz2_32_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨35, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 35 (by decide)))

theorem fz2_32_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨36, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 36 (by decide)))

theorem fz2_32_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨37, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 37 (by decide)))

theorem fz2_32_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨38, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 38 (by decide)))

theorem fz2_32_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨39, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 39 (by decide)))

theorem fz2_32_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨40, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 40 (by decide)))

theorem fz2_32_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨41, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 41 (by decide)))

theorem fz2_32_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨42, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 42 (by decide)))

theorem fz2_32_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨43, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 43 (by decide)))

theorem fz2_32_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨44, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 44 (by decide)))

theorem fz2_32_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨45, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 45 (by decide)))

theorem fz2_32_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨46, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 46 (by decide)))

theorem fz2_32_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨47, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 47 (by decide)))

theorem fz2_32_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨48, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 48 (by decide)))

theorem fz2_32_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨49, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 49 (by decide)))

theorem fz2_32_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨50, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 50 (by decide)))

theorem fz2_32_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨51, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 51 (by decide)))

theorem fz2_32_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨52, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 52 (by decide)))

theorem fz2_32_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨53, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 53 (by decide)))

theorem fz2_32_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK32)) = 0 :=
  Q2.repsFixedCard2 rK32 ⟨54, by decide⟩ Q2.R32_2 Q2.hpxR32_2 Q2.hcardq32_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_32) 54 (by decide)))

end LeanDring.P5Presentation
