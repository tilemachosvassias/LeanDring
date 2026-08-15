/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C026

/-!
# Species-table cells, off-support emptiness certificates, chunk 37

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

theorem fixz1_38 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK38) (retConj 1 (R38 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_38_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨1, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 1 (by decide)))

theorem fz1_38_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨2, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 2 (by decide)))

theorem fz1_38_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨3, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 3 (by decide)))

theorem fz1_38_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨4, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 4 (by decide)))

theorem fz1_38_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨5, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 5 (by decide)))

theorem fz1_38_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨6, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 6 (by decide)))

theorem fz1_38_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨7, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 7 (by decide)))

theorem fz1_38_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨8, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 8 (by decide)))

theorem fz1_38_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨9, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 9 (by decide)))

theorem fz1_38_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨10, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 10 (by decide)))

theorem fz1_38_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨11, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 11 (by decide)))

theorem fz1_38_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨13, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 13 (by decide)))

theorem fz1_38_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨14, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 14 (by decide)))

theorem fz1_38_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨15, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 15 (by decide)))

theorem fz1_38_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨16, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 16 (by decide)))

theorem fz1_38_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨17, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 17 (by decide)))

theorem fz1_38_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨18, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 18 (by decide)))

theorem fz1_38_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨19, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 19 (by decide)))

theorem fz1_38_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨20, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 20 (by decide)))

theorem fz1_38_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨21, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 21 (by decide)))

theorem fz1_38_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨22, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 22 (by decide)))

theorem fz1_38_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨23, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 23 (by decide)))

theorem fz1_38_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨24, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 24 (by decide)))

theorem fz1_38_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨25, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 25 (by decide)))

theorem fz1_38_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨26, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 26 (by decide)))

theorem fz1_38_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨27, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 27 (by decide)))

theorem fz1_38_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨28, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 28 (by decide)))

theorem fz1_38_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨29, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 29 (by decide)))

theorem fz1_38_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨30, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 30 (by decide)))

theorem fz1_38_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨31, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 31 (by decide)))

theorem fz1_38_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨32, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 32 (by decide)))

theorem fz1_38_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨33, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 33 (by decide)))

theorem fz1_38_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨34, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 34 (by decide)))

theorem fz1_38_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨35, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 35 (by decide)))

theorem fz1_38_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨36, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 36 (by decide)))

theorem fz1_38_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨37, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 37 (by decide)))

theorem fz1_38_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨39, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 39 (by decide)))

theorem fz1_38_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨40, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 40 (by decide)))

theorem fz1_38_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨41, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 41 (by decide)))

theorem fz1_38_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨42, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 42 (by decide)))

theorem fz1_38_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨43, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 43 (by decide)))

theorem fz1_38_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨44, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 44 (by decide)))

theorem fz1_38_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨45, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 45 (by decide)))

theorem fz1_38_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨46, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 46 (by decide)))

theorem fz1_38_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨47, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 47 (by decide)))

theorem fz1_38_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨48, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 48 (by decide)))

theorem fz1_38_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨49, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 49 (by decide)))

theorem fz1_38_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨50, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 50 (by decide)))

theorem fz1_38_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨51, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 51 (by decide)))

theorem fz1_38_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨52, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 52 (by decide)))

theorem fz1_38_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨53, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 53 (by decide)))

theorem fz1_38_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK38)) = 0 :=
  repsFixedCard rK38 ⟨54, by decide⟩ R38 hpxR38 hcardq38
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_38) 54 (by decide)))

theorem fixz2_38 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK38) (retConj 2 (Q2.R38_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_38_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨1, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 1 (by decide)))

theorem fz2_38_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨2, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 2 (by decide)))

theorem fz2_38_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨3, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 3 (by decide)))

theorem fz2_38_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨4, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 4 (by decide)))

theorem fz2_38_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨5, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 5 (by decide)))

theorem fz2_38_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨6, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 6 (by decide)))

theorem fz2_38_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨7, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 7 (by decide)))

theorem fz2_38_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨8, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 8 (by decide)))

theorem fz2_38_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨9, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 9 (by decide)))

theorem fz2_38_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨10, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 10 (by decide)))

theorem fz2_38_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨11, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 11 (by decide)))

theorem fz2_38_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨13, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 13 (by decide)))

theorem fz2_38_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨14, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 14 (by decide)))

theorem fz2_38_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨15, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 15 (by decide)))

theorem fz2_38_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨16, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 16 (by decide)))

theorem fz2_38_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨17, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 17 (by decide)))

theorem fz2_38_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨18, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 18 (by decide)))

theorem fz2_38_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨19, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 19 (by decide)))

theorem fz2_38_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨20, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 20 (by decide)))

theorem fz2_38_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨21, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 21 (by decide)))

theorem fz2_38_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨22, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 22 (by decide)))

theorem fz2_38_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨23, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 23 (by decide)))

theorem fz2_38_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨24, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 24 (by decide)))

theorem fz2_38_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨25, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 25 (by decide)))

theorem fz2_38_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨26, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 26 (by decide)))

theorem fz2_38_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨27, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 27 (by decide)))

theorem fz2_38_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨28, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 28 (by decide)))

theorem fz2_38_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨29, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 29 (by decide)))

theorem fz2_38_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨30, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 30 (by decide)))

theorem fz2_38_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨31, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 31 (by decide)))

theorem fz2_38_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨32, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 32 (by decide)))

theorem fz2_38_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨33, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 33 (by decide)))

theorem fz2_38_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨34, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 34 (by decide)))

theorem fz2_38_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨35, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 35 (by decide)))

theorem fz2_38_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨36, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 36 (by decide)))

theorem fz2_38_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨37, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 37 (by decide)))

theorem fz2_38_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨39, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 39 (by decide)))

theorem fz2_38_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨40, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 40 (by decide)))

theorem fz2_38_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨41, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 41 (by decide)))

theorem fz2_38_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨42, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 42 (by decide)))

theorem fz2_38_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨43, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 43 (by decide)))

theorem fz2_38_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨44, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 44 (by decide)))

theorem fz2_38_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨45, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 45 (by decide)))

theorem fz2_38_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨46, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 46 (by decide)))

theorem fz2_38_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨47, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 47 (by decide)))

theorem fz2_38_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨48, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 48 (by decide)))

theorem fz2_38_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨49, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 49 (by decide)))

theorem fz2_38_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨50, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 50 (by decide)))

theorem fz2_38_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨51, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 51 (by decide)))

theorem fz2_38_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨52, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 52 (by decide)))

theorem fz2_38_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨53, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 53 (by decide)))

theorem fz2_38_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK38)) = 0 :=
  Q2.repsFixedCard2 rK38 ⟨54, by decide⟩ Q2.R38_2 Q2.hpxR38_2 Q2.hcardq38_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_38) 54 (by decide)))

end LeanDring.P5Presentation
