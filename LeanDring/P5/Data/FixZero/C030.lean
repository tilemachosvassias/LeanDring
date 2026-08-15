/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C018

/-!
# Species-table cells, off-support emptiness certificates, chunk 29

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

theorem fixz1_30 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK30) (retConj 1 (R30 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_30_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨1, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 1 (by decide)))

theorem fz1_30_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨2, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 2 (by decide)))

theorem fz1_30_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨3, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 3 (by decide)))

theorem fz1_30_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨4, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 4 (by decide)))

theorem fz1_30_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨5, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 5 (by decide)))

theorem fz1_30_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨6, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 6 (by decide)))

theorem fz1_30_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨7, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 7 (by decide)))

theorem fz1_30_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨8, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 8 (by decide)))

theorem fz1_30_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨9, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 9 (by decide)))

theorem fz1_30_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨10, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 10 (by decide)))

theorem fz1_30_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨11, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 11 (by decide)))

theorem fz1_30_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨13, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 13 (by decide)))

theorem fz1_30_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨14, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 14 (by decide)))

theorem fz1_30_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨15, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 15 (by decide)))

theorem fz1_30_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨16, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 16 (by decide)))

theorem fz1_30_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨17, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 17 (by decide)))

theorem fz1_30_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨18, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 18 (by decide)))

theorem fz1_30_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨19, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 19 (by decide)))

theorem fz1_30_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨20, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 20 (by decide)))

theorem fz1_30_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨21, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 21 (by decide)))

theorem fz1_30_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨22, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 22 (by decide)))

theorem fz1_30_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨23, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 23 (by decide)))

theorem fz1_30_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨24, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 24 (by decide)))

theorem fz1_30_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨25, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 25 (by decide)))

theorem fz1_30_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨26, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 26 (by decide)))

theorem fz1_30_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨27, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 27 (by decide)))

theorem fz1_30_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨28, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 28 (by decide)))

theorem fz1_30_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨29, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 29 (by decide)))

theorem fz1_30_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨31, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 31 (by decide)))

theorem fz1_30_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨32, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 32 (by decide)))

theorem fz1_30_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨33, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 33 (by decide)))

theorem fz1_30_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨34, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 34 (by decide)))

theorem fz1_30_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨35, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 35 (by decide)))

theorem fz1_30_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨36, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 36 (by decide)))

theorem fz1_30_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨37, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 37 (by decide)))

theorem fz1_30_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨38, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 38 (by decide)))

theorem fz1_30_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨39, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 39 (by decide)))

theorem fz1_30_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨40, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 40 (by decide)))

theorem fz1_30_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨41, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 41 (by decide)))

theorem fz1_30_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨42, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 42 (by decide)))

theorem fz1_30_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨43, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 43 (by decide)))

theorem fz1_30_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨44, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 44 (by decide)))

theorem fz1_30_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨45, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 45 (by decide)))

theorem fz1_30_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨46, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 46 (by decide)))

theorem fz1_30_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨47, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 47 (by decide)))

theorem fz1_30_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨48, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 48 (by decide)))

theorem fz1_30_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨49, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 49 (by decide)))

theorem fz1_30_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨50, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 50 (by decide)))

theorem fz1_30_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨51, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 51 (by decide)))

theorem fz1_30_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨52, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 52 (by decide)))

theorem fz1_30_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨53, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 53 (by decide)))

theorem fz1_30_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK30)) = 0 :=
  repsFixedCard rK30 ⟨54, by decide⟩ R30 hpxR30 hcardq30
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_30) 54 (by decide)))

theorem fixz2_30 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK30) (retConj 2 (Q2.R30_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_30_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨1, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 1 (by decide)))

theorem fz2_30_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨2, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 2 (by decide)))

theorem fz2_30_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨3, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 3 (by decide)))

theorem fz2_30_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨4, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 4 (by decide)))

theorem fz2_30_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨5, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 5 (by decide)))

theorem fz2_30_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨6, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 6 (by decide)))

theorem fz2_30_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨7, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 7 (by decide)))

theorem fz2_30_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨8, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 8 (by decide)))

theorem fz2_30_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨9, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 9 (by decide)))

theorem fz2_30_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨10, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 10 (by decide)))

theorem fz2_30_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨11, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 11 (by decide)))

theorem fz2_30_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨13, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 13 (by decide)))

theorem fz2_30_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨14, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 14 (by decide)))

theorem fz2_30_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨15, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 15 (by decide)))

theorem fz2_30_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨16, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 16 (by decide)))

theorem fz2_30_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨17, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 17 (by decide)))

theorem fz2_30_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨18, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 18 (by decide)))

theorem fz2_30_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨19, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 19 (by decide)))

theorem fz2_30_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨20, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 20 (by decide)))

theorem fz2_30_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨21, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 21 (by decide)))

theorem fz2_30_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨22, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 22 (by decide)))

theorem fz2_30_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨23, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 23 (by decide)))

theorem fz2_30_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨24, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 24 (by decide)))

theorem fz2_30_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨25, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 25 (by decide)))

theorem fz2_30_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨26, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 26 (by decide)))

theorem fz2_30_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨27, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 27 (by decide)))

theorem fz2_30_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨28, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 28 (by decide)))

theorem fz2_30_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨29, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 29 (by decide)))

theorem fz2_30_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨31, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 31 (by decide)))

theorem fz2_30_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨32, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 32 (by decide)))

theorem fz2_30_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨33, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 33 (by decide)))

theorem fz2_30_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨34, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 34 (by decide)))

theorem fz2_30_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨35, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 35 (by decide)))

theorem fz2_30_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨36, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 36 (by decide)))

theorem fz2_30_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨37, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 37 (by decide)))

theorem fz2_30_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨38, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 38 (by decide)))

theorem fz2_30_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨39, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 39 (by decide)))

theorem fz2_30_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨40, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 40 (by decide)))

theorem fz2_30_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨41, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 41 (by decide)))

theorem fz2_30_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨42, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 42 (by decide)))

theorem fz2_30_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨43, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 43 (by decide)))

theorem fz2_30_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨44, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 44 (by decide)))

theorem fz2_30_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨45, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 45 (by decide)))

theorem fz2_30_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨46, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 46 (by decide)))

theorem fz2_30_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨47, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 47 (by decide)))

theorem fz2_30_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨48, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 48 (by decide)))

theorem fz2_30_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨49, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 49 (by decide)))

theorem fz2_30_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨50, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 50 (by decide)))

theorem fz2_30_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨51, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 51 (by decide)))

theorem fz2_30_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨52, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 52 (by decide)))

theorem fz2_30_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨53, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 53 (by decide)))

theorem fz2_30_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK30)) = 0 :=
  Q2.repsFixedCard2 rK30 ⟨54, by decide⟩ Q2.R30_2 Q2.hpxR30_2 Q2.hcardq30_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_30) 54 (by decide)))

end LeanDring.P5Presentation
