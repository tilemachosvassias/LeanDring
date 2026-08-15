/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C042

/-!
# Species-table cells, off-support emptiness certificates, chunk 53

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

theorem fixz1_54 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK54) (retConj 1 (R54 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_54_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨1, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 1 (by decide)))

theorem fz1_54_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨2, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 2 (by decide)))

theorem fz1_54_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨3, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 3 (by decide)))

theorem fz1_54_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨4, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 4 (by decide)))

theorem fz1_54_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨5, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 5 (by decide)))

theorem fz1_54_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨6, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 6 (by decide)))

theorem fz1_54_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨7, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 7 (by decide)))

theorem fz1_54_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨8, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 8 (by decide)))

theorem fz1_54_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨9, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 9 (by decide)))

theorem fz1_54_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨10, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 10 (by decide)))

theorem fz1_54_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨13, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 13 (by decide)))

theorem fz1_54_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨14, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 14 (by decide)))

theorem fz1_54_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨15, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 15 (by decide)))

theorem fz1_54_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨16, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 16 (by decide)))

theorem fz1_54_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨17, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 17 (by decide)))

theorem fz1_54_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨18, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 18 (by decide)))

theorem fz1_54_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨19, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 19 (by decide)))

theorem fz1_54_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨20, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 20 (by decide)))

theorem fz1_54_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨21, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 21 (by decide)))

theorem fz1_54_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨22, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 22 (by decide)))

theorem fz1_54_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨23, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 23 (by decide)))

theorem fz1_54_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨24, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 24 (by decide)))

theorem fz1_54_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨25, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 25 (by decide)))

theorem fz1_54_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨26, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 26 (by decide)))

theorem fz1_54_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨27, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 27 (by decide)))

theorem fz1_54_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨28, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 28 (by decide)))

theorem fz1_54_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨29, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 29 (by decide)))

theorem fz1_54_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨30, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 30 (by decide)))

theorem fz1_54_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨31, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 31 (by decide)))

theorem fz1_54_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨32, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 32 (by decide)))

theorem fz1_54_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨33, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 33 (by decide)))

theorem fz1_54_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨34, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 34 (by decide)))

theorem fz1_54_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨35, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 35 (by decide)))

theorem fz1_54_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨36, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 36 (by decide)))

theorem fz1_54_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨37, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 37 (by decide)))

theorem fz1_54_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨38, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 38 (by decide)))

theorem fz1_54_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨39, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 39 (by decide)))

theorem fz1_54_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨40, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 40 (by decide)))

theorem fz1_54_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨41, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 41 (by decide)))

theorem fz1_54_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨42, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 42 (by decide)))

theorem fz1_54_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨43, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 43 (by decide)))

theorem fz1_54_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨44, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 44 (by decide)))

theorem fz1_54_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨45, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 45 (by decide)))

theorem fz1_54_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨46, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 46 (by decide)))

theorem fz1_54_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨47, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 47 (by decide)))

theorem fz1_54_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨48, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 48 (by decide)))

theorem fz1_54_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨49, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 49 (by decide)))

theorem fz1_54_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨50, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 50 (by decide)))

theorem fz1_54_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨51, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 51 (by decide)))

theorem fz1_54_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨52, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 52 (by decide)))

theorem fz1_54_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK54)) = 0 :=
  repsFixedCard rK54 ⟨53, by decide⟩ R54 hpxR54 hcardq54
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_54) 53 (by decide)))

theorem fixz2_54 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK54) (retConj 2 (Q2.R54_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_54_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨1, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 1 (by decide)))

theorem fz2_54_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨2, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 2 (by decide)))

theorem fz2_54_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨3, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 3 (by decide)))

theorem fz2_54_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨4, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 4 (by decide)))

theorem fz2_54_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨5, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 5 (by decide)))

theorem fz2_54_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨6, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 6 (by decide)))

theorem fz2_54_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨7, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 7 (by decide)))

theorem fz2_54_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨8, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 8 (by decide)))

theorem fz2_54_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨9, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 9 (by decide)))

theorem fz2_54_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨10, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 10 (by decide)))

theorem fz2_54_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨13, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 13 (by decide)))

theorem fz2_54_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨14, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 14 (by decide)))

theorem fz2_54_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨15, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 15 (by decide)))

theorem fz2_54_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨16, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 16 (by decide)))

theorem fz2_54_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨17, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 17 (by decide)))

theorem fz2_54_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨18, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 18 (by decide)))

theorem fz2_54_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨19, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 19 (by decide)))

theorem fz2_54_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨20, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 20 (by decide)))

theorem fz2_54_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨21, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 21 (by decide)))

theorem fz2_54_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨22, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 22 (by decide)))

theorem fz2_54_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨23, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 23 (by decide)))

theorem fz2_54_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨24, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 24 (by decide)))

theorem fz2_54_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨25, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 25 (by decide)))

theorem fz2_54_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨26, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 26 (by decide)))

theorem fz2_54_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨27, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 27 (by decide)))

theorem fz2_54_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨28, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 28 (by decide)))

theorem fz2_54_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨29, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 29 (by decide)))

theorem fz2_54_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨30, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 30 (by decide)))

theorem fz2_54_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨31, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 31 (by decide)))

theorem fz2_54_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨32, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 32 (by decide)))

theorem fz2_54_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨33, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 33 (by decide)))

theorem fz2_54_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨34, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 34 (by decide)))

theorem fz2_54_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨35, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 35 (by decide)))

theorem fz2_54_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨36, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 36 (by decide)))

theorem fz2_54_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨37, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 37 (by decide)))

theorem fz2_54_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨38, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 38 (by decide)))

theorem fz2_54_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨39, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 39 (by decide)))

theorem fz2_54_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨40, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 40 (by decide)))

theorem fz2_54_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨41, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 41 (by decide)))

theorem fz2_54_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨42, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 42 (by decide)))

theorem fz2_54_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨43, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 43 (by decide)))

theorem fz2_54_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨44, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 44 (by decide)))

theorem fz2_54_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨45, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 45 (by decide)))

theorem fz2_54_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨46, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 46 (by decide)))

theorem fz2_54_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨47, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 47 (by decide)))

theorem fz2_54_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨48, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 48 (by decide)))

theorem fz2_54_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨49, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 49 (by decide)))

theorem fz2_54_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨50, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 50 (by decide)))

theorem fz2_54_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨51, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 51 (by decide)))

theorem fz2_54_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨52, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 52 (by decide)))

theorem fz2_54_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK54)) = 0 :=
  Q2.repsFixedCard2 rK54 ⟨53, by decide⟩ Q2.R54_2 Q2.hpxR54_2 Q2.hcardq54_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_54) 53 (by decide)))

end LeanDring.P5Presentation
