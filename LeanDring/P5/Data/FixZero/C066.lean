/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C018

/-!
# Species-table cells, off-support emptiness certificates, chunk 65

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

theorem fixz1_77 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK77) (retConj 1 (R77 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_77_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨1, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 1 (by decide)))

theorem fz1_77_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨2, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 2 (by decide)))

theorem fz1_77_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨3, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 3 (by decide)))

theorem fz1_77_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨4, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 4 (by decide)))

theorem fz1_77_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨5, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 5 (by decide)))

theorem fz1_77_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨6, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 6 (by decide)))

theorem fz1_77_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨8, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 8 (by decide)))

theorem fz1_77_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨9, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 9 (by decide)))

theorem fz1_77_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨10, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 10 (by decide)))

theorem fz1_77_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨11, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 11 (by decide)))

theorem fz1_77_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨13, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 13 (by decide)))

theorem fz1_77_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨14, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 14 (by decide)))

theorem fz1_77_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨15, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 15 (by decide)))

theorem fz1_77_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨16, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 16 (by decide)))

theorem fz1_77_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨17, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 17 (by decide)))

theorem fz1_77_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨18, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 18 (by decide)))

theorem fz1_77_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨19, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 19 (by decide)))

theorem fz1_77_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨20, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 20 (by decide)))

theorem fz1_77_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨21, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 21 (by decide)))

theorem fz1_77_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨22, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 22 (by decide)))

theorem fz1_77_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨23, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 23 (by decide)))

theorem fz1_77_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨24, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 24 (by decide)))

theorem fz1_77_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨26, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 26 (by decide)))

theorem fz1_77_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨27, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 27 (by decide)))

theorem fz1_77_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨28, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 28 (by decide)))

theorem fz1_77_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨29, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 29 (by decide)))

theorem fz1_77_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨30, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 30 (by decide)))

theorem fz1_77_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨31, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 31 (by decide)))

theorem fz1_77_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨33, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 33 (by decide)))

theorem fz1_77_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨34, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 34 (by decide)))

theorem fz1_77_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨35, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 35 (by decide)))

theorem fz1_77_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨36, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 36 (by decide)))

theorem fz1_77_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨38, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 38 (by decide)))

theorem fz1_77_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨39, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 39 (by decide)))

theorem fz1_77_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨40, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 40 (by decide)))

theorem fz1_77_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨41, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 41 (by decide)))

theorem fz1_77_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨43, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 43 (by decide)))

theorem fz1_77_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨44, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 44 (by decide)))

theorem fz1_77_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨45, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 45 (by decide)))

theorem fz1_77_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨46, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 46 (by decide)))

theorem fz1_77_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨48, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 48 (by decide)))

theorem fz1_77_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨49, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 49 (by decide)))

theorem fz1_77_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨50, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 50 (by decide)))

theorem fz1_77_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨51, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 51 (by decide)))

theorem fz1_77_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨53, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 53 (by decide)))

theorem fz1_77_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨54, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 54 (by decide)))

theorem fz1_77_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨55, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 55 (by decide)))

theorem fz1_77_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨56, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 56 (by decide)))

theorem fz1_77_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨57, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 57 (by decide)))

theorem fz1_77_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨58, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 58 (by decide)))

theorem fz1_77_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨59, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 59 (by decide)))

theorem fz1_77_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨60, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 60 (by decide)))

theorem fz1_77_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨61, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 61 (by decide)))

theorem fz1_77_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨62, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 62 (by decide)))

theorem fz1_77_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨63, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 63 (by decide)))

theorem fz1_77_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨64, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 64 (by decide)))

theorem fz1_77_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨65, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 65 (by decide)))

theorem fz1_77_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨66, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 66 (by decide)))

theorem fz1_77_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨67, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 67 (by decide)))

theorem fz1_77_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨68, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 68 (by decide)))

theorem fz1_77_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨69, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 69 (by decide)))

theorem fz1_77_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨70, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 70 (by decide)))

theorem fz1_77_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨71, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 71 (by decide)))

theorem fz1_77_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨72, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 72 (by decide)))

theorem fz1_77_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨73, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 73 (by decide)))

theorem fz1_77_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨74, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 74 (by decide)))

theorem fz1_77_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨75, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 75 (by decide)))

theorem fz1_77_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨76, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 76 (by decide)))

theorem fz1_77_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨78, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 78 (by decide)))

theorem fz1_77_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨79, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 79 (by decide)))

theorem fz1_77_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨80, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 80 (by decide)))

theorem fz1_77_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨81, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 81 (by decide)))

theorem fz1_77_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨82, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 82 (by decide)))

theorem fz1_77_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨83, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 83 (by decide)))

theorem fz1_77_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨84, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 84 (by decide)))

theorem fz1_77_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨85, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 85 (by decide)))

theorem fz1_77_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨86, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 86 (by decide)))

theorem fz1_77_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨87, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 87 (by decide)))

theorem fz1_77_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨88, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 88 (by decide)))

theorem fz1_77_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨89, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 89 (by decide)))

theorem fz1_77_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨90, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 90 (by decide)))

theorem fz1_77_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨91, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 91 (by decide)))

theorem fz1_77_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨92, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 92 (by decide)))

theorem fz1_77_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨93, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 93 (by decide)))

theorem fz1_77_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨94, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 94 (by decide)))

theorem fz1_77_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨95, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 95 (by decide)))

theorem fz1_77_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨96, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 96 (by decide)))

theorem fz1_77_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨97, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 97 (by decide)))

theorem fz1_77_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨98, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 98 (by decide)))

theorem fz1_77_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨99, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 99 (by decide)))

theorem fz1_77_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨100, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 100 (by decide)))

theorem fz1_77_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨101, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 101 (by decide)))

theorem fz1_77_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨102, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 102 (by decide)))

theorem fz1_77_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨103, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 103 (by decide)))

theorem fz1_77_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨104, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 104 (by decide)))

theorem fz1_77_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨105, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 105 (by decide)))

theorem fz1_77_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨106, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 106 (by decide)))

theorem fz1_77_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨107, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 107 (by decide)))

theorem fz1_77_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨108, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 108 (by decide)))

theorem fz1_77_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨109, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 109 (by decide)))

theorem fz1_77_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨110, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 110 (by decide)))

theorem fz1_77_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨111, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 111 (by decide)))

theorem fz1_77_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨112, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 112 (by decide)))

theorem fz1_77_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨113, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 113 (by decide)))

theorem fz1_77_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨114, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 114 (by decide)))

theorem fz1_77_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK77)) = 0 :=
  repsFixedCard rK77 ⟨115, by decide⟩ R77 hpxR77 hcardq77
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_77) 115 (by decide)))

theorem fixz2_77 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK77) (retConj 2 (Q2.R77_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_77_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨1, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 1 (by decide)))

theorem fz2_77_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨2, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 2 (by decide)))

theorem fz2_77_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨3, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 3 (by decide)))

theorem fz2_77_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨4, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 4 (by decide)))

theorem fz2_77_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨5, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 5 (by decide)))

theorem fz2_77_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨6, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 6 (by decide)))

theorem fz2_77_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨8, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 8 (by decide)))

theorem fz2_77_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨9, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 9 (by decide)))

theorem fz2_77_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨10, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 10 (by decide)))

theorem fz2_77_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨11, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 11 (by decide)))

theorem fz2_77_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨13, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 13 (by decide)))

theorem fz2_77_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨14, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 14 (by decide)))

theorem fz2_77_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨15, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 15 (by decide)))

theorem fz2_77_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨16, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 16 (by decide)))

theorem fz2_77_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨17, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 17 (by decide)))

theorem fz2_77_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨18, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 18 (by decide)))

theorem fz2_77_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨19, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 19 (by decide)))

theorem fz2_77_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨20, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 20 (by decide)))

theorem fz2_77_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨21, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 21 (by decide)))

theorem fz2_77_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨22, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 22 (by decide)))

theorem fz2_77_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨23, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 23 (by decide)))

theorem fz2_77_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨24, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 24 (by decide)))

theorem fz2_77_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨26, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 26 (by decide)))

theorem fz2_77_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨27, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 27 (by decide)))

theorem fz2_77_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨28, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 28 (by decide)))

theorem fz2_77_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨29, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 29 (by decide)))

theorem fz2_77_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨30, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 30 (by decide)))

theorem fz2_77_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨31, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 31 (by decide)))

theorem fz2_77_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨33, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 33 (by decide)))

theorem fz2_77_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨34, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 34 (by decide)))

theorem fz2_77_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨35, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 35 (by decide)))

theorem fz2_77_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨36, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 36 (by decide)))

theorem fz2_77_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨38, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 38 (by decide)))

theorem fz2_77_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨39, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 39 (by decide)))

theorem fz2_77_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨40, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 40 (by decide)))

theorem fz2_77_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨41, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 41 (by decide)))

theorem fz2_77_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨43, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 43 (by decide)))

theorem fz2_77_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨44, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 44 (by decide)))

theorem fz2_77_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨45, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 45 (by decide)))

theorem fz2_77_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨46, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 46 (by decide)))

theorem fz2_77_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨48, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 48 (by decide)))

theorem fz2_77_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨49, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 49 (by decide)))

theorem fz2_77_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨50, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 50 (by decide)))

theorem fz2_77_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨51, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 51 (by decide)))

theorem fz2_77_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨53, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 53 (by decide)))

theorem fz2_77_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨54, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 54 (by decide)))

theorem fz2_77_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨55, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 55 (by decide)))

theorem fz2_77_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨56, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 56 (by decide)))

theorem fz2_77_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨57, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 57 (by decide)))

theorem fz2_77_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨58, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 58 (by decide)))

theorem fz2_77_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨59, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 59 (by decide)))

theorem fz2_77_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨60, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 60 (by decide)))

theorem fz2_77_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨61, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 61 (by decide)))

theorem fz2_77_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨62, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 62 (by decide)))

theorem fz2_77_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨63, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 63 (by decide)))

theorem fz2_77_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨64, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 64 (by decide)))

theorem fz2_77_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨65, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 65 (by decide)))

theorem fz2_77_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨66, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 66 (by decide)))

theorem fz2_77_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨67, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 67 (by decide)))

theorem fz2_77_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨68, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 68 (by decide)))

theorem fz2_77_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨69, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 69 (by decide)))

theorem fz2_77_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨70, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 70 (by decide)))

theorem fz2_77_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨71, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 71 (by decide)))

theorem fz2_77_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨72, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 72 (by decide)))

theorem fz2_77_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨73, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 73 (by decide)))

theorem fz2_77_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨74, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 74 (by decide)))

theorem fz2_77_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨75, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 75 (by decide)))

theorem fz2_77_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨76, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 76 (by decide)))

theorem fz2_77_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨78, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 78 (by decide)))

theorem fz2_77_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨79, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 79 (by decide)))

theorem fz2_77_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨80, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 80 (by decide)))

theorem fz2_77_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨81, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 81 (by decide)))

theorem fz2_77_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨82, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 82 (by decide)))

theorem fz2_77_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨83, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 83 (by decide)))

theorem fz2_77_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨84, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 84 (by decide)))

theorem fz2_77_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨85, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 85 (by decide)))

theorem fz2_77_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨86, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 86 (by decide)))

theorem fz2_77_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨87, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 87 (by decide)))

theorem fz2_77_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨88, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 88 (by decide)))

theorem fz2_77_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨89, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 89 (by decide)))

theorem fz2_77_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨90, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 90 (by decide)))

theorem fz2_77_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨91, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 91 (by decide)))

theorem fz2_77_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨92, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 92 (by decide)))

theorem fz2_77_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨93, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 93 (by decide)))

theorem fz2_77_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨94, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 94 (by decide)))

theorem fz2_77_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨95, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 95 (by decide)))

theorem fz2_77_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨96, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 96 (by decide)))

theorem fz2_77_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨97, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 97 (by decide)))

theorem fz2_77_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨98, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 98 (by decide)))

theorem fz2_77_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨99, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 99 (by decide)))

theorem fz2_77_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨100, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 100 (by decide)))

theorem fz2_77_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨101, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 101 (by decide)))

theorem fz2_77_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨102, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 102 (by decide)))

theorem fz2_77_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨103, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 103 (by decide)))

theorem fz2_77_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨104, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 104 (by decide)))

theorem fz2_77_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨105, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 105 (by decide)))

theorem fz2_77_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨106, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 106 (by decide)))

theorem fz2_77_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨107, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 107 (by decide)))

theorem fz2_77_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨108, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 108 (by decide)))

theorem fz2_77_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨109, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 109 (by decide)))

theorem fz2_77_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨110, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 110 (by decide)))

theorem fz2_77_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨111, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 111 (by decide)))

theorem fz2_77_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨112, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 112 (by decide)))

theorem fz2_77_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨113, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 113 (by decide)))

theorem fz2_77_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨114, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 114 (by decide)))

theorem fz2_77_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK77)) = 0 :=
  Q2.repsFixedCard2 rK77 ⟨115, by decide⟩ Q2.R77_2 Q2.hpxR77_2 Q2.hcardq77_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_77) 115 (by decide)))

theorem fixz1_78 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK78) (retConj 1 (R78 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_78_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨1, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 1 (by decide)))

theorem fz1_78_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨2, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 2 (by decide)))

theorem fz1_78_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨3, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 3 (by decide)))

theorem fz1_78_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨4, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 4 (by decide)))

theorem fz1_78_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨5, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 5 (by decide)))

theorem fz1_78_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨7, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 7 (by decide)))

theorem fz1_78_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨8, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 8 (by decide)))

theorem fz1_78_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨9, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 9 (by decide)))

theorem fz1_78_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨10, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 10 (by decide)))

theorem fz1_78_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨11, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 11 (by decide)))

theorem fz1_78_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨13, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 13 (by decide)))

theorem fz1_78_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨14, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 14 (by decide)))

theorem fz1_78_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨15, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 15 (by decide)))

theorem fz1_78_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨16, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 16 (by decide)))

theorem fz1_78_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨17, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 17 (by decide)))

theorem fz1_78_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨18, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 18 (by decide)))

theorem fz1_78_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨19, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 19 (by decide)))

theorem fz1_78_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨20, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 20 (by decide)))

theorem fz1_78_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨21, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 21 (by decide)))

theorem fz1_78_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨22, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 22 (by decide)))

theorem fz1_78_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨23, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 23 (by decide)))

theorem fz1_78_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨25, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 25 (by decide)))

theorem fz1_78_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨26, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 26 (by decide)))

theorem fz1_78_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨27, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 27 (by decide)))

theorem fz1_78_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨28, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 28 (by decide)))

theorem fz1_78_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨29, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 29 (by decide)))

theorem fz1_78_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨30, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 30 (by decide)))

theorem fz1_78_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨31, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 31 (by decide)))

theorem fz1_78_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨33, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 33 (by decide)))

theorem fz1_78_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨34, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 34 (by decide)))

theorem fz1_78_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨35, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 35 (by decide)))

theorem fz1_78_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨36, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 36 (by decide)))

theorem fz1_78_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨38, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 38 (by decide)))

theorem fz1_78_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨39, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 39 (by decide)))

theorem fz1_78_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨40, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 40 (by decide)))

theorem fz1_78_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨41, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 41 (by decide)))

theorem fz1_78_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨43, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 43 (by decide)))

theorem fz1_78_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨44, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 44 (by decide)))

theorem fz1_78_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨45, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 45 (by decide)))

theorem fz1_78_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨46, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 46 (by decide)))

theorem fz1_78_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨48, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 48 (by decide)))

theorem fz1_78_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨49, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 49 (by decide)))

theorem fz1_78_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨50, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 50 (by decide)))

theorem fz1_78_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨51, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 51 (by decide)))

theorem fz1_78_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨53, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 53 (by decide)))

theorem fz1_78_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨54, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 54 (by decide)))

theorem fz1_78_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨55, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 55 (by decide)))

theorem fz1_78_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨56, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 56 (by decide)))

theorem fz1_78_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨57, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 57 (by decide)))

theorem fz1_78_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨58, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 58 (by decide)))

theorem fz1_78_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨59, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 59 (by decide)))

theorem fz1_78_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨60, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 60 (by decide)))

theorem fz1_78_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨61, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 61 (by decide)))

theorem fz1_78_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨62, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 62 (by decide)))

theorem fz1_78_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨63, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 63 (by decide)))

theorem fz1_78_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨64, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 64 (by decide)))

theorem fz1_78_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨65, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 65 (by decide)))

theorem fz1_78_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨66, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 66 (by decide)))

theorem fz1_78_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨67, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 67 (by decide)))

theorem fz1_78_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨68, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 68 (by decide)))

theorem fz1_78_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨69, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 69 (by decide)))

theorem fz1_78_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨70, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 70 (by decide)))

theorem fz1_78_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨71, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 71 (by decide)))

theorem fz1_78_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨72, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 72 (by decide)))

theorem fz1_78_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨73, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 73 (by decide)))

theorem fz1_78_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨74, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 74 (by decide)))

theorem fz1_78_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨75, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 75 (by decide)))

theorem fz1_78_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨76, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 76 (by decide)))

theorem fz1_78_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨77, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 77 (by decide)))

theorem fz1_78_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨79, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 79 (by decide)))

theorem fz1_78_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨80, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 80 (by decide)))

theorem fz1_78_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨81, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 81 (by decide)))

theorem fz1_78_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨82, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 82 (by decide)))

theorem fz1_78_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨83, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 83 (by decide)))

theorem fz1_78_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨84, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 84 (by decide)))

theorem fz1_78_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨85, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 85 (by decide)))

theorem fz1_78_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨86, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 86 (by decide)))

theorem fz1_78_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨87, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 87 (by decide)))

theorem fz1_78_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨88, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 88 (by decide)))

theorem fz1_78_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨89, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 89 (by decide)))

theorem fz1_78_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨90, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 90 (by decide)))

theorem fz1_78_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨91, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 91 (by decide)))

theorem fz1_78_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨92, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 92 (by decide)))

theorem fz1_78_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨93, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 93 (by decide)))

theorem fz1_78_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨94, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 94 (by decide)))

theorem fz1_78_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨95, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 95 (by decide)))

theorem fz1_78_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨96, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 96 (by decide)))

theorem fz1_78_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨97, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 97 (by decide)))

theorem fz1_78_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨98, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 98 (by decide)))

theorem fz1_78_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨99, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 99 (by decide)))

theorem fz1_78_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨100, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 100 (by decide)))

theorem fz1_78_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨101, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 101 (by decide)))

theorem fz1_78_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨102, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 102 (by decide)))

theorem fz1_78_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨103, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 103 (by decide)))

theorem fz1_78_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨104, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 104 (by decide)))

theorem fz1_78_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨105, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 105 (by decide)))

theorem fz1_78_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨106, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 106 (by decide)))

theorem fz1_78_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨107, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 107 (by decide)))

theorem fz1_78_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨108, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 108 (by decide)))

theorem fz1_78_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨109, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 109 (by decide)))

theorem fz1_78_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨110, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 110 (by decide)))

theorem fz1_78_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨111, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 111 (by decide)))

theorem fz1_78_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨112, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 112 (by decide)))

theorem fz1_78_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨113, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 113 (by decide)))

theorem fz1_78_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨114, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 114 (by decide)))

theorem fz1_78_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK78)) = 0 :=
  repsFixedCard rK78 ⟨115, by decide⟩ R78 hpxR78 hcardq78
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_78) 115 (by decide)))

theorem fixz2_78 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK78) (retConj 2 (Q2.R78_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_78_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨1, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 1 (by decide)))

theorem fz2_78_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨2, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 2 (by decide)))

theorem fz2_78_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨3, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 3 (by decide)))

theorem fz2_78_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨4, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 4 (by decide)))

theorem fz2_78_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨5, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 5 (by decide)))

theorem fz2_78_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨7, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 7 (by decide)))

theorem fz2_78_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨8, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 8 (by decide)))

theorem fz2_78_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨9, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 9 (by decide)))

theorem fz2_78_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨10, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 10 (by decide)))

theorem fz2_78_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨11, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 11 (by decide)))

theorem fz2_78_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨13, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 13 (by decide)))

theorem fz2_78_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨14, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 14 (by decide)))

theorem fz2_78_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨15, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 15 (by decide)))

theorem fz2_78_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨16, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 16 (by decide)))

theorem fz2_78_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨17, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 17 (by decide)))

theorem fz2_78_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨18, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 18 (by decide)))

theorem fz2_78_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨19, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 19 (by decide)))

theorem fz2_78_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨20, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 20 (by decide)))

theorem fz2_78_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨21, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 21 (by decide)))

theorem fz2_78_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨22, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 22 (by decide)))

theorem fz2_78_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨23, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 23 (by decide)))

theorem fz2_78_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨25, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 25 (by decide)))

theorem fz2_78_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨26, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 26 (by decide)))

theorem fz2_78_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨27, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 27 (by decide)))

theorem fz2_78_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨28, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 28 (by decide)))

theorem fz2_78_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨29, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 29 (by decide)))

theorem fz2_78_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨30, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 30 (by decide)))

theorem fz2_78_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨31, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 31 (by decide)))

theorem fz2_78_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨33, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 33 (by decide)))

theorem fz2_78_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨34, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 34 (by decide)))

theorem fz2_78_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨35, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 35 (by decide)))

theorem fz2_78_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨36, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 36 (by decide)))

theorem fz2_78_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨38, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 38 (by decide)))

theorem fz2_78_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨39, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 39 (by decide)))

theorem fz2_78_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨40, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 40 (by decide)))

theorem fz2_78_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨41, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 41 (by decide)))

theorem fz2_78_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨43, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 43 (by decide)))

theorem fz2_78_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨44, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 44 (by decide)))

theorem fz2_78_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨45, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 45 (by decide)))

theorem fz2_78_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨46, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 46 (by decide)))

theorem fz2_78_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨48, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 48 (by decide)))

theorem fz2_78_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨49, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 49 (by decide)))

theorem fz2_78_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨50, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 50 (by decide)))

theorem fz2_78_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨51, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 51 (by decide)))

theorem fz2_78_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨53, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 53 (by decide)))

theorem fz2_78_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨54, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 54 (by decide)))

theorem fz2_78_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨55, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 55 (by decide)))

theorem fz2_78_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨56, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 56 (by decide)))

theorem fz2_78_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨57, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 57 (by decide)))

theorem fz2_78_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨58, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 58 (by decide)))

theorem fz2_78_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨59, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 59 (by decide)))

theorem fz2_78_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨60, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 60 (by decide)))

theorem fz2_78_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨61, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 61 (by decide)))

theorem fz2_78_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨62, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 62 (by decide)))

theorem fz2_78_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨63, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 63 (by decide)))

theorem fz2_78_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨64, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 64 (by decide)))

theorem fz2_78_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨65, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 65 (by decide)))

theorem fz2_78_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨66, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 66 (by decide)))

theorem fz2_78_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨67, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 67 (by decide)))

theorem fz2_78_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨68, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 68 (by decide)))

theorem fz2_78_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨69, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 69 (by decide)))

theorem fz2_78_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨70, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 70 (by decide)))

theorem fz2_78_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨71, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 71 (by decide)))

theorem fz2_78_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨72, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 72 (by decide)))

theorem fz2_78_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨73, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 73 (by decide)))

theorem fz2_78_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨74, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 74 (by decide)))

theorem fz2_78_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨75, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 75 (by decide)))

theorem fz2_78_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨76, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 76 (by decide)))

theorem fz2_78_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨77, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 77 (by decide)))

theorem fz2_78_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨79, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 79 (by decide)))

theorem fz2_78_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨80, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 80 (by decide)))

theorem fz2_78_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨81, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 81 (by decide)))

theorem fz2_78_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨82, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 82 (by decide)))

theorem fz2_78_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨83, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 83 (by decide)))

theorem fz2_78_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨84, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 84 (by decide)))

theorem fz2_78_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨85, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 85 (by decide)))

theorem fz2_78_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨86, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 86 (by decide)))

theorem fz2_78_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨87, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 87 (by decide)))

theorem fz2_78_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨88, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 88 (by decide)))

theorem fz2_78_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨89, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 89 (by decide)))

theorem fz2_78_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨90, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 90 (by decide)))

theorem fz2_78_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨91, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 91 (by decide)))

theorem fz2_78_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨92, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 92 (by decide)))

theorem fz2_78_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨93, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 93 (by decide)))

theorem fz2_78_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨94, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 94 (by decide)))

theorem fz2_78_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨95, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 95 (by decide)))

theorem fz2_78_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨96, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 96 (by decide)))

theorem fz2_78_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨97, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 97 (by decide)))

theorem fz2_78_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨98, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 98 (by decide)))

theorem fz2_78_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨99, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 99 (by decide)))

theorem fz2_78_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨100, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 100 (by decide)))

theorem fz2_78_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨101, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 101 (by decide)))

theorem fz2_78_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨102, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 102 (by decide)))

theorem fz2_78_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨103, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 103 (by decide)))

theorem fz2_78_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨104, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 104 (by decide)))

theorem fz2_78_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨105, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 105 (by decide)))

theorem fz2_78_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨106, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 106 (by decide)))

theorem fz2_78_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨107, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 107 (by decide)))

theorem fz2_78_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨108, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 108 (by decide)))

theorem fz2_78_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨109, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 109 (by decide)))

theorem fz2_78_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨110, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 110 (by decide)))

theorem fz2_78_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨111, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 111 (by decide)))

theorem fz2_78_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨112, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 112 (by decide)))

theorem fz2_78_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨113, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 113 (by decide)))

theorem fz2_78_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨114, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 114 (by decide)))

theorem fz2_78_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK78)) = 0 :=
  Q2.repsFixedCard2 rK78 ⟨115, by decide⟩ Q2.R78_2 Q2.hpxR78_2 Q2.hcardq78_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_78) 115 (by decide)))

end LeanDring.P5Presentation
