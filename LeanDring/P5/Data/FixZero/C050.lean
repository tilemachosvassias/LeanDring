/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C038

/-!
# Species-table cells, off-support emptiness certificates, chunk 49

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

theorem fixz1_50 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK50) (retConj 1 (R50 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_50_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨1, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 1 (by decide)))

theorem fz1_50_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨2, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 2 (by decide)))

theorem fz1_50_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨3, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 3 (by decide)))

theorem fz1_50_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨4, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 4 (by decide)))

theorem fz1_50_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨5, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 5 (by decide)))

theorem fz1_50_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨6, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 6 (by decide)))

theorem fz1_50_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨7, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 7 (by decide)))

theorem fz1_50_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨8, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 8 (by decide)))

theorem fz1_50_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨9, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 9 (by decide)))

theorem fz1_50_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨10, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 10 (by decide)))

theorem fz1_50_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨11, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 11 (by decide)))

theorem fz1_50_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨13, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 13 (by decide)))

theorem fz1_50_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨14, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 14 (by decide)))

theorem fz1_50_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨15, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 15 (by decide)))

theorem fz1_50_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨16, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 16 (by decide)))

theorem fz1_50_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨17, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 17 (by decide)))

theorem fz1_50_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨18, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 18 (by decide)))

theorem fz1_50_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨19, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 19 (by decide)))

theorem fz1_50_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨20, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 20 (by decide)))

theorem fz1_50_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨21, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 21 (by decide)))

theorem fz1_50_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨22, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 22 (by decide)))

theorem fz1_50_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨23, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 23 (by decide)))

theorem fz1_50_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨24, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 24 (by decide)))

theorem fz1_50_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨25, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 25 (by decide)))

theorem fz1_50_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨26, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 26 (by decide)))

theorem fz1_50_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨27, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 27 (by decide)))

theorem fz1_50_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨28, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 28 (by decide)))

theorem fz1_50_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨29, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 29 (by decide)))

theorem fz1_50_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨30, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 30 (by decide)))

theorem fz1_50_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨31, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 31 (by decide)))

theorem fz1_50_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨32, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 32 (by decide)))

theorem fz1_50_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨33, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 33 (by decide)))

theorem fz1_50_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨34, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 34 (by decide)))

theorem fz1_50_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨35, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 35 (by decide)))

theorem fz1_50_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨36, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 36 (by decide)))

theorem fz1_50_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨37, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 37 (by decide)))

theorem fz1_50_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨38, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 38 (by decide)))

theorem fz1_50_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨39, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 39 (by decide)))

theorem fz1_50_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨40, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 40 (by decide)))

theorem fz1_50_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨41, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 41 (by decide)))

theorem fz1_50_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨42, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 42 (by decide)))

theorem fz1_50_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨43, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 43 (by decide)))

theorem fz1_50_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨44, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 44 (by decide)))

theorem fz1_50_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨45, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 45 (by decide)))

theorem fz1_50_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨46, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 46 (by decide)))

theorem fz1_50_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨47, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 47 (by decide)))

theorem fz1_50_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨48, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 48 (by decide)))

theorem fz1_50_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨49, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 49 (by decide)))

theorem fz1_50_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨51, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 51 (by decide)))

theorem fz1_50_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨52, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 52 (by decide)))

theorem fz1_50_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨53, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 53 (by decide)))

theorem fz1_50_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK50)) = 0 :=
  repsFixedCard rK50 ⟨54, by decide⟩ R50 hpxR50 hcardq50
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_50) 54 (by decide)))

theorem fixz2_50 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK50) (retConj 2 (Q2.R50_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_50_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨1, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 1 (by decide)))

theorem fz2_50_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨2, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 2 (by decide)))

theorem fz2_50_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨3, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 3 (by decide)))

theorem fz2_50_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨4, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 4 (by decide)))

theorem fz2_50_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨5, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 5 (by decide)))

theorem fz2_50_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨6, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 6 (by decide)))

theorem fz2_50_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨7, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 7 (by decide)))

theorem fz2_50_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨8, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 8 (by decide)))

theorem fz2_50_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨9, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 9 (by decide)))

theorem fz2_50_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨10, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 10 (by decide)))

theorem fz2_50_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨11, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 11 (by decide)))

theorem fz2_50_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨13, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 13 (by decide)))

theorem fz2_50_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨14, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 14 (by decide)))

theorem fz2_50_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨15, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 15 (by decide)))

theorem fz2_50_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨16, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 16 (by decide)))

theorem fz2_50_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨17, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 17 (by decide)))

theorem fz2_50_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨18, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 18 (by decide)))

theorem fz2_50_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨19, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 19 (by decide)))

theorem fz2_50_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨20, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 20 (by decide)))

theorem fz2_50_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨21, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 21 (by decide)))

theorem fz2_50_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨22, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 22 (by decide)))

theorem fz2_50_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨23, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 23 (by decide)))

theorem fz2_50_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨24, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 24 (by decide)))

theorem fz2_50_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨25, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 25 (by decide)))

theorem fz2_50_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨26, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 26 (by decide)))

theorem fz2_50_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨27, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 27 (by decide)))

theorem fz2_50_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨28, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 28 (by decide)))

theorem fz2_50_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨29, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 29 (by decide)))

theorem fz2_50_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨30, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 30 (by decide)))

theorem fz2_50_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨31, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 31 (by decide)))

theorem fz2_50_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨32, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 32 (by decide)))

theorem fz2_50_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨33, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 33 (by decide)))

theorem fz2_50_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨34, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 34 (by decide)))

theorem fz2_50_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨35, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 35 (by decide)))

theorem fz2_50_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨36, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 36 (by decide)))

theorem fz2_50_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨37, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 37 (by decide)))

theorem fz2_50_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨38, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 38 (by decide)))

theorem fz2_50_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨39, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 39 (by decide)))

theorem fz2_50_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨40, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 40 (by decide)))

theorem fz2_50_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨41, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 41 (by decide)))

theorem fz2_50_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨42, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 42 (by decide)))

theorem fz2_50_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨43, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 43 (by decide)))

theorem fz2_50_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨44, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 44 (by decide)))

theorem fz2_50_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨45, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 45 (by decide)))

theorem fz2_50_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨46, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 46 (by decide)))

theorem fz2_50_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨47, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 47 (by decide)))

theorem fz2_50_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨48, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 48 (by decide)))

theorem fz2_50_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨49, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 49 (by decide)))

theorem fz2_50_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨51, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 51 (by decide)))

theorem fz2_50_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨52, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 52 (by decide)))

theorem fz2_50_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨53, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 53 (by decide)))

theorem fz2_50_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK50)) = 0 :=
  Q2.repsFixedCard2 rK50 ⟨54, by decide⟩ Q2.R50_2 Q2.hpxR50_2 Q2.hcardq50_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_50) 54 (by decide)))

end LeanDring.P5Presentation
