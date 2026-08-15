/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C012

/-!
# Species-table cells, off-support emptiness certificates, chunk 23

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

theorem fixz1_24 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK24) (retConj 1 (R24 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_24_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨1, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 1 (by decide)))

theorem fz1_24_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨2, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 2 (by decide)))

theorem fz1_24_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨3, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 3 (by decide)))

theorem fz1_24_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨4, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 4 (by decide)))

theorem fz1_24_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨5, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 5 (by decide)))

theorem fz1_24_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨7, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 7 (by decide)))

theorem fz1_24_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨8, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 8 (by decide)))

theorem fz1_24_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨9, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 9 (by decide)))

theorem fz1_24_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨10, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 10 (by decide)))

theorem fz1_24_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨11, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 11 (by decide)))

theorem fz1_24_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨13, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 13 (by decide)))

theorem fz1_24_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨14, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 14 (by decide)))

theorem fz1_24_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨15, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 15 (by decide)))

theorem fz1_24_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨16, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 16 (by decide)))

theorem fz1_24_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨17, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 17 (by decide)))

theorem fz1_24_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨18, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 18 (by decide)))

theorem fz1_24_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨19, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 19 (by decide)))

theorem fz1_24_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨20, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 20 (by decide)))

theorem fz1_24_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨21, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 21 (by decide)))

theorem fz1_24_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨22, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 22 (by decide)))

theorem fz1_24_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨23, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 23 (by decide)))

theorem fz1_24_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨25, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 25 (by decide)))

theorem fz1_24_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨26, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 26 (by decide)))

theorem fz1_24_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨27, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 27 (by decide)))

theorem fz1_24_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨28, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 28 (by decide)))

theorem fz1_24_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨29, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 29 (by decide)))

theorem fz1_24_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨30, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 30 (by decide)))

theorem fz1_24_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨31, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 31 (by decide)))

theorem fz1_24_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨32, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 32 (by decide)))

theorem fz1_24_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨33, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 33 (by decide)))

theorem fz1_24_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨34, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 34 (by decide)))

theorem fz1_24_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨35, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 35 (by decide)))

theorem fz1_24_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨36, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 36 (by decide)))

theorem fz1_24_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨37, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 37 (by decide)))

theorem fz1_24_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨38, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 38 (by decide)))

theorem fz1_24_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨39, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 39 (by decide)))

theorem fz1_24_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨40, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 40 (by decide)))

theorem fz1_24_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨41, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 41 (by decide)))

theorem fz1_24_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨42, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 42 (by decide)))

theorem fz1_24_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨43, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 43 (by decide)))

theorem fz1_24_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨44, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 44 (by decide)))

theorem fz1_24_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨45, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 45 (by decide)))

theorem fz1_24_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨46, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 46 (by decide)))

theorem fz1_24_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨47, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 47 (by decide)))

theorem fz1_24_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨48, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 48 (by decide)))

theorem fz1_24_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨49, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 49 (by decide)))

theorem fz1_24_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨50, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 50 (by decide)))

theorem fz1_24_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨51, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 51 (by decide)))

theorem fz1_24_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨52, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 52 (by decide)))

theorem fz1_24_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨53, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 53 (by decide)))

theorem fz1_24_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK24)) = 0 :=
  repsFixedCard rK24 ⟨54, by decide⟩ R24 hpxR24 hcardq24
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_24) 54 (by decide)))

theorem fixz2_24 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK24) (retConj 2 (Q2.R24_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_24_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨1, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 1 (by decide)))

theorem fz2_24_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨2, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 2 (by decide)))

theorem fz2_24_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨3, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 3 (by decide)))

theorem fz2_24_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨4, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 4 (by decide)))

theorem fz2_24_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨5, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 5 (by decide)))

theorem fz2_24_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨7, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 7 (by decide)))

theorem fz2_24_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨8, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 8 (by decide)))

theorem fz2_24_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨9, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 9 (by decide)))

theorem fz2_24_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨10, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 10 (by decide)))

theorem fz2_24_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨11, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 11 (by decide)))

theorem fz2_24_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨13, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 13 (by decide)))

theorem fz2_24_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨14, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 14 (by decide)))

theorem fz2_24_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨15, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 15 (by decide)))

theorem fz2_24_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨16, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 16 (by decide)))

theorem fz2_24_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨17, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 17 (by decide)))

theorem fz2_24_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨18, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 18 (by decide)))

theorem fz2_24_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨19, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 19 (by decide)))

theorem fz2_24_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨20, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 20 (by decide)))

theorem fz2_24_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨21, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 21 (by decide)))

theorem fz2_24_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨22, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 22 (by decide)))

theorem fz2_24_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨23, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 23 (by decide)))

theorem fz2_24_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨25, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 25 (by decide)))

theorem fz2_24_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨26, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 26 (by decide)))

theorem fz2_24_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨27, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 27 (by decide)))

theorem fz2_24_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨28, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 28 (by decide)))

theorem fz2_24_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨29, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 29 (by decide)))

theorem fz2_24_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨30, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 30 (by decide)))

theorem fz2_24_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨31, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 31 (by decide)))

theorem fz2_24_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨32, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 32 (by decide)))

theorem fz2_24_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨33, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 33 (by decide)))

theorem fz2_24_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨34, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 34 (by decide)))

theorem fz2_24_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨35, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 35 (by decide)))

theorem fz2_24_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨36, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 36 (by decide)))

theorem fz2_24_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨37, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 37 (by decide)))

theorem fz2_24_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨38, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 38 (by decide)))

theorem fz2_24_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨39, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 39 (by decide)))

theorem fz2_24_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨40, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 40 (by decide)))

theorem fz2_24_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨41, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 41 (by decide)))

theorem fz2_24_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨42, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 42 (by decide)))

theorem fz2_24_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨43, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 43 (by decide)))

theorem fz2_24_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨44, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 44 (by decide)))

theorem fz2_24_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨45, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 45 (by decide)))

theorem fz2_24_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨46, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 46 (by decide)))

theorem fz2_24_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨47, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 47 (by decide)))

theorem fz2_24_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨48, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 48 (by decide)))

theorem fz2_24_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨49, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 49 (by decide)))

theorem fz2_24_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨50, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 50 (by decide)))

theorem fz2_24_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨51, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 51 (by decide)))

theorem fz2_24_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨52, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 52 (by decide)))

theorem fz2_24_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨53, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 53 (by decide)))

theorem fz2_24_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK24)) = 0 :=
  Q2.repsFixedCard2 rK24 ⟨54, by decide⟩ Q2.R24_2 Q2.hpxR24_2 Q2.hcardq24_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_24) 54 (by decide)))

end LeanDring.P5Presentation
