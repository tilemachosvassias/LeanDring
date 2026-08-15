/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C024
import LeanDring.P5.Data.EntryK.C025
import LeanDring.P5.Data.EntryK.C026
import LeanDring.P5.Data.EntryK.C027
import LeanDring.P5.Data.EntryK.C028
import LeanDring.P5.Data.EntryK.C029

/-!
# Species-table cells, off-support emptiness certificates, chunk 84

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

theorem fixz1_115 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK115) (retConj 1 (R115 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_115_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨1, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 1 (by decide)))

theorem fz1_115_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨2, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 2 (by decide)))

theorem fz1_115_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨3, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 3 (by decide)))

theorem fz1_115_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨4, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 4 (by decide)))

theorem fz1_115_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨5, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 5 (by decide)))

theorem fz1_115_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨6, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 6 (by decide)))

theorem fz1_115_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨7, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 7 (by decide)))

theorem fz1_115_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨8, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 8 (by decide)))

theorem fz1_115_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨9, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 9 (by decide)))

theorem fz1_115_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨13, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 13 (by decide)))

theorem fz1_115_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨14, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 14 (by decide)))

theorem fz1_115_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨15, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 15 (by decide)))

theorem fz1_115_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨16, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 16 (by decide)))

theorem fz1_115_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨17, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 17 (by decide)))

theorem fz1_115_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨18, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 18 (by decide)))

theorem fz1_115_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨19, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 19 (by decide)))

theorem fz1_115_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨20, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 20 (by decide)))

theorem fz1_115_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨21, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 21 (by decide)))

theorem fz1_115_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨22, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 22 (by decide)))

theorem fz1_115_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨23, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 23 (by decide)))

theorem fz1_115_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨24, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 24 (by decide)))

theorem fz1_115_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨25, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 25 (by decide)))

theorem fz1_115_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨26, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 26 (by decide)))

theorem fz1_115_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨27, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 27 (by decide)))

theorem fz1_115_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨28, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 28 (by decide)))

theorem fz1_115_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨29, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 29 (by decide)))

theorem fz1_115_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨30, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 30 (by decide)))

theorem fz1_115_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨31, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 31 (by decide)))

theorem fz1_115_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨32, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 32 (by decide)))

theorem fz1_115_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨33, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 33 (by decide)))

theorem fz1_115_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨34, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 34 (by decide)))

theorem fz1_115_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨35, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 35 (by decide)))

theorem fz1_115_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨36, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 36 (by decide)))

theorem fz1_115_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨37, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 37 (by decide)))

theorem fz1_115_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨38, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 38 (by decide)))

theorem fz1_115_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨39, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 39 (by decide)))

theorem fz1_115_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨40, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 40 (by decide)))

theorem fz1_115_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨41, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 41 (by decide)))

theorem fz1_115_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨42, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 42 (by decide)))

theorem fz1_115_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨43, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 43 (by decide)))

theorem fz1_115_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨44, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 44 (by decide)))

theorem fz1_115_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨45, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 45 (by decide)))

theorem fz1_115_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨46, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 46 (by decide)))

theorem fz1_115_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨47, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 47 (by decide)))

theorem fz1_115_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨48, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 48 (by decide)))

theorem fz1_115_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨49, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 49 (by decide)))

theorem fz1_115_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨50, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 50 (by decide)))

theorem fz1_115_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨51, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 51 (by decide)))

theorem fz1_115_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨52, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 52 (by decide)))

theorem fz1_115_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨55, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 55 (by decide)))

theorem fz1_115_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨56, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 56 (by decide)))

theorem fz1_115_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨57, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 57 (by decide)))

theorem fz1_115_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨58, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 58 (by decide)))

theorem fz1_115_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨59, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 59 (by decide)))

theorem fz1_115_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨60, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 60 (by decide)))

theorem fz1_115_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨61, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 61 (by decide)))

theorem fz1_115_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨62, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 62 (by decide)))

theorem fz1_115_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨63, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 63 (by decide)))

theorem fz1_115_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨64, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 64 (by decide)))

theorem fz1_115_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨65, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 65 (by decide)))

theorem fz1_115_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨66, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 66 (by decide)))

theorem fz1_115_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨67, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 67 (by decide)))

theorem fz1_115_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨68, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 68 (by decide)))

theorem fz1_115_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨69, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 69 (by decide)))

theorem fz1_115_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨70, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 70 (by decide)))

theorem fz1_115_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨71, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 71 (by decide)))

theorem fz1_115_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨72, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 72 (by decide)))

theorem fz1_115_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨73, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 73 (by decide)))

theorem fz1_115_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨74, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 74 (by decide)))

theorem fz1_115_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨75, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 75 (by decide)))

theorem fz1_115_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨76, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 76 (by decide)))

theorem fz1_115_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨77, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 77 (by decide)))

theorem fz1_115_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨78, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 78 (by decide)))

theorem fz1_115_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨79, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 79 (by decide)))

theorem fz1_115_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨80, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 80 (by decide)))

theorem fz1_115_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨81, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 81 (by decide)))

theorem fz1_115_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨82, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 82 (by decide)))

theorem fz1_115_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨83, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 83 (by decide)))

theorem fz1_115_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨84, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 84 (by decide)))

theorem fz1_115_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨85, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 85 (by decide)))

theorem fz1_115_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨86, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 86 (by decide)))

theorem fz1_115_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨87, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 87 (by decide)))

theorem fz1_115_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨88, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 88 (by decide)))

theorem fz1_115_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨89, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 89 (by decide)))

theorem fz1_115_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨90, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 90 (by decide)))

theorem fz1_115_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨91, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 91 (by decide)))

theorem fz1_115_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨92, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 92 (by decide)))

theorem fz1_115_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨93, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 93 (by decide)))

theorem fz1_115_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨94, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 94 (by decide)))

theorem fz1_115_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨95, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 95 (by decide)))

theorem fz1_115_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨96, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 96 (by decide)))

theorem fz1_115_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨97, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 97 (by decide)))

theorem fz1_115_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨98, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 98 (by decide)))

theorem fz1_115_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨99, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 99 (by decide)))

theorem fz1_115_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨100, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 100 (by decide)))

theorem fz1_115_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨101, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 101 (by decide)))

theorem fz1_115_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨102, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 102 (by decide)))

theorem fz1_115_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨103, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 103 (by decide)))

theorem fz1_115_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨104, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 104 (by decide)))

theorem fz1_115_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨105, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 105 (by decide)))

theorem fz1_115_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨106, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 106 (by decide)))

theorem fz1_115_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨107, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 107 (by decide)))

theorem fz1_115_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨108, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 108 (by decide)))

theorem fz1_115_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨109, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 109 (by decide)))

theorem fz1_115_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨110, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 110 (by decide)))

theorem fz1_115_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨111, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 111 (by decide)))

theorem fz1_115_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨112, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 112 (by decide)))

theorem fz1_115_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨113, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 113 (by decide)))

theorem fz1_115_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK115)) = 0 :=
  repsFixedCard rK115 ⟨114, by decide⟩ R115 hpxR115 hcardq115
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_115) 114 (by decide)))

theorem fixz2_115 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK115) (retConj 2 (Q2.R115_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_115_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨1, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 1 (by decide)))

theorem fz2_115_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨2, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 2 (by decide)))

theorem fz2_115_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨3, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 3 (by decide)))

theorem fz2_115_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨4, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 4 (by decide)))

theorem fz2_115_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨5, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 5 (by decide)))

theorem fz2_115_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨6, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 6 (by decide)))

theorem fz2_115_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨7, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 7 (by decide)))

theorem fz2_115_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨8, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 8 (by decide)))

theorem fz2_115_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨9, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 9 (by decide)))

theorem fz2_115_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨13, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 13 (by decide)))

theorem fz2_115_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨14, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 14 (by decide)))

theorem fz2_115_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨15, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 15 (by decide)))

theorem fz2_115_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨16, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 16 (by decide)))

theorem fz2_115_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨17, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 17 (by decide)))

theorem fz2_115_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨18, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 18 (by decide)))

theorem fz2_115_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨19, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 19 (by decide)))

theorem fz2_115_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨20, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 20 (by decide)))

theorem fz2_115_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨21, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 21 (by decide)))

theorem fz2_115_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨22, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 22 (by decide)))

theorem fz2_115_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨23, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 23 (by decide)))

theorem fz2_115_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨24, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 24 (by decide)))

theorem fz2_115_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨25, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 25 (by decide)))

theorem fz2_115_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨26, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 26 (by decide)))

theorem fz2_115_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨27, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 27 (by decide)))

theorem fz2_115_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨28, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 28 (by decide)))

theorem fz2_115_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨29, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 29 (by decide)))

theorem fz2_115_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨30, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 30 (by decide)))

theorem fz2_115_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨31, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 31 (by decide)))

theorem fz2_115_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨32, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 32 (by decide)))

theorem fz2_115_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨33, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 33 (by decide)))

theorem fz2_115_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨34, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 34 (by decide)))

theorem fz2_115_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨35, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 35 (by decide)))

theorem fz2_115_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨36, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 36 (by decide)))

theorem fz2_115_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨37, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 37 (by decide)))

theorem fz2_115_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨38, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 38 (by decide)))

theorem fz2_115_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨39, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 39 (by decide)))

theorem fz2_115_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨40, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 40 (by decide)))

theorem fz2_115_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨41, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 41 (by decide)))

theorem fz2_115_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨42, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 42 (by decide)))

theorem fz2_115_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨43, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 43 (by decide)))

theorem fz2_115_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨44, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 44 (by decide)))

theorem fz2_115_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨45, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 45 (by decide)))

theorem fz2_115_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨46, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 46 (by decide)))

theorem fz2_115_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨47, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 47 (by decide)))

theorem fz2_115_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨48, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 48 (by decide)))

theorem fz2_115_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨49, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 49 (by decide)))

theorem fz2_115_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨50, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 50 (by decide)))

theorem fz2_115_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨51, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 51 (by decide)))

theorem fz2_115_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨52, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 52 (by decide)))

theorem fz2_115_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨55, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 55 (by decide)))

theorem fz2_115_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨56, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 56 (by decide)))

theorem fz2_115_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨57, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 57 (by decide)))

theorem fz2_115_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨58, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 58 (by decide)))

theorem fz2_115_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨59, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 59 (by decide)))

theorem fz2_115_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨60, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 60 (by decide)))

theorem fz2_115_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨61, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 61 (by decide)))

theorem fz2_115_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨62, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 62 (by decide)))

theorem fz2_115_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨63, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 63 (by decide)))

theorem fz2_115_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨64, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 64 (by decide)))

theorem fz2_115_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨65, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 65 (by decide)))

theorem fz2_115_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨66, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 66 (by decide)))

theorem fz2_115_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨67, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 67 (by decide)))

theorem fz2_115_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨68, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 68 (by decide)))

theorem fz2_115_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨69, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 69 (by decide)))

theorem fz2_115_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨70, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 70 (by decide)))

theorem fz2_115_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨71, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 71 (by decide)))

theorem fz2_115_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨72, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 72 (by decide)))

theorem fz2_115_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨73, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 73 (by decide)))

theorem fz2_115_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨74, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 74 (by decide)))

theorem fz2_115_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨75, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 75 (by decide)))

theorem fz2_115_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨76, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 76 (by decide)))

theorem fz2_115_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨77, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 77 (by decide)))

theorem fz2_115_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨78, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 78 (by decide)))

theorem fz2_115_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨79, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 79 (by decide)))

theorem fz2_115_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨80, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 80 (by decide)))

theorem fz2_115_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨81, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 81 (by decide)))

theorem fz2_115_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨82, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 82 (by decide)))

theorem fz2_115_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨83, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 83 (by decide)))

theorem fz2_115_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨84, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 84 (by decide)))

theorem fz2_115_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨85, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 85 (by decide)))

theorem fz2_115_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨86, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 86 (by decide)))

theorem fz2_115_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨87, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 87 (by decide)))

theorem fz2_115_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨88, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 88 (by decide)))

theorem fz2_115_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨89, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 89 (by decide)))

theorem fz2_115_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨90, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 90 (by decide)))

theorem fz2_115_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨91, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 91 (by decide)))

theorem fz2_115_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨92, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 92 (by decide)))

theorem fz2_115_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨93, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 93 (by decide)))

theorem fz2_115_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨94, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 94 (by decide)))

theorem fz2_115_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨95, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 95 (by decide)))

theorem fz2_115_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨96, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 96 (by decide)))

theorem fz2_115_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨97, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 97 (by decide)))

theorem fz2_115_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨98, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 98 (by decide)))

theorem fz2_115_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨99, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 99 (by decide)))

theorem fz2_115_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨100, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 100 (by decide)))

theorem fz2_115_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨101, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 101 (by decide)))

theorem fz2_115_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨102, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 102 (by decide)))

theorem fz2_115_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨103, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 103 (by decide)))

theorem fz2_115_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨104, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 104 (by decide)))

theorem fz2_115_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨105, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 105 (by decide)))

theorem fz2_115_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨106, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 106 (by decide)))

theorem fz2_115_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨107, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 107 (by decide)))

theorem fz2_115_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨108, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 108 (by decide)))

theorem fz2_115_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨109, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 109 (by decide)))

theorem fz2_115_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨110, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 110 (by decide)))

theorem fz2_115_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨111, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 111 (by decide)))

theorem fz2_115_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨112, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 112 (by decide)))

theorem fz2_115_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨113, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 113 (by decide)))

theorem fz2_115_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK115)) = 0 :=
  Q2.repsFixedCard2 rK115 ⟨114, by decide⟩ Q2.R115_2 Q2.hpxR115_2 Q2.hcardq115_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_115) 114 (by decide)))

theorem fixz1_116 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 54, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 84, 85, 86, 87, 88, 89, 91, 92, 93, 94, 96, 97, 98, 99, 101, 102, 103, 104, 106, 107, 108, 109, 111, 112, 113, 114, 115, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK116) (retConj 1 (R116 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_116_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨2, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 2 (by decide)))

theorem fz1_116_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨3, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 3 (by decide)))

theorem fz1_116_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨4, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 4 (by decide)))

theorem fz1_116_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨5, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 5 (by decide)))

theorem fz1_116_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨11, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 11 (by decide)))

theorem fz1_116_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨14, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 14 (by decide)))

theorem fz1_116_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨15, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 15 (by decide)))

theorem fz1_116_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨16, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 16 (by decide)))

theorem fz1_116_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨17, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 17 (by decide)))

theorem fz1_116_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨18, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 18 (by decide)))

theorem fz1_116_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨20, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 20 (by decide)))

theorem fz1_116_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨21, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 21 (by decide)))

theorem fz1_116_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨22, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 22 (by decide)))

theorem fz1_116_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨23, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 23 (by decide)))

theorem fz1_116_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨29, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 29 (by decide)))

theorem fz1_116_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨30, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 30 (by decide)))

theorem fz1_116_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨31, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 31 (by decide)))

theorem fz1_116_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨32, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 32 (by decide)))

theorem fz1_116_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨34, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 34 (by decide)))

theorem fz1_116_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨35, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 35 (by decide)))

theorem fz1_116_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨36, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 36 (by decide)))

theorem fz1_116_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨37, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 37 (by decide)))

theorem fz1_116_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨39, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 39 (by decide)))

theorem fz1_116_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨40, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 40 (by decide)))

theorem fz1_116_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨41, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 41 (by decide)))

theorem fz1_116_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨42, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 42 (by decide)))

theorem fz1_116_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨44, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 44 (by decide)))

theorem fz1_116_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨45, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 45 (by decide)))

theorem fz1_116_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨46, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 46 (by decide)))

theorem fz1_116_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨47, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 47 (by decide)))

theorem fz1_116_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨49, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 49 (by decide)))

theorem fz1_116_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨50, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 50 (by decide)))

theorem fz1_116_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨51, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 51 (by decide)))

theorem fz1_116_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨52, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 52 (by decide)))

theorem fz1_116_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨54, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 54 (by decide)))

theorem fz1_116_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨60, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 60 (by decide)))

theorem fz1_116_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨61, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 61 (by decide)))

theorem fz1_116_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨62, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 62 (by decide)))

theorem fz1_116_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨63, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 63 (by decide)))

theorem fz1_116_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨64, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 64 (by decide)))

theorem fz1_116_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨65, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 65 (by decide)))

theorem fz1_116_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨66, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 66 (by decide)))

theorem fz1_116_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨67, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 67 (by decide)))

theorem fz1_116_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨68, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 68 (by decide)))

theorem fz1_116_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨69, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 69 (by decide)))

theorem fz1_116_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨70, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 70 (by decide)))

theorem fz1_116_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨71, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 71 (by decide)))

theorem fz1_116_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨72, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 72 (by decide)))

theorem fz1_116_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨73, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 73 (by decide)))

theorem fz1_116_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨74, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 74 (by decide)))

theorem fz1_116_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨75, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 75 (by decide)))

theorem fz1_116_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨76, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 76 (by decide)))

theorem fz1_116_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨77, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 77 (by decide)))

theorem fz1_116_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨78, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 78 (by decide)))

theorem fz1_116_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨79, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 79 (by decide)))

theorem fz1_116_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨81, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 81 (by decide)))

theorem fz1_116_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨82, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 82 (by decide)))

theorem fz1_116_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨83, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 83 (by decide)))

theorem fz1_116_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨84, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 84 (by decide)))

theorem fz1_116_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨85, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 85 (by decide)))

theorem fz1_116_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨86, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 86 (by decide)))

theorem fz1_116_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨87, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 87 (by decide)))

theorem fz1_116_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨88, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 88 (by decide)))

theorem fz1_116_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨89, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 89 (by decide)))

theorem fz1_116_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨91, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 91 (by decide)))

theorem fz1_116_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨92, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 92 (by decide)))

theorem fz1_116_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨93, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 93 (by decide)))

theorem fz1_116_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨94, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 94 (by decide)))

theorem fz1_116_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨96, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 96 (by decide)))

theorem fz1_116_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨97, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 97 (by decide)))

theorem fz1_116_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨98, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 98 (by decide)))

theorem fz1_116_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨99, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 99 (by decide)))

theorem fz1_116_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨101, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 101 (by decide)))

theorem fz1_116_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨102, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 102 (by decide)))

theorem fz1_116_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨103, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 103 (by decide)))

theorem fz1_116_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨104, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 104 (by decide)))

theorem fz1_116_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨106, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 106 (by decide)))

theorem fz1_116_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨107, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 107 (by decide)))

theorem fz1_116_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨108, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 108 (by decide)))

theorem fz1_116_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨109, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 109 (by decide)))

theorem fz1_116_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨111, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 111 (by decide)))

theorem fz1_116_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨112, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 112 (by decide)))

theorem fz1_116_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨113, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 113 (by decide)))

theorem fz1_116_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨114, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 114 (by decide)))

theorem fz1_116_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨115, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 115 (by decide)))

theorem fz1_116_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨117, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 117 (by decide)))

theorem fz1_116_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨118, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 118 (by decide)))

theorem fz1_116_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨119, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 119 (by decide)))

theorem fz1_116_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨120, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 120 (by decide)))

theorem fz1_116_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨121, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 121 (by decide)))

theorem fz1_116_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨122, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 122 (by decide)))

theorem fz1_116_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨123, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 123 (by decide)))

theorem fz1_116_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨124, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 124 (by decide)))

theorem fz1_116_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨125, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 125 (by decide)))

theorem fz1_116_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨126, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 126 (by decide)))

theorem fz1_116_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨127, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 127 (by decide)))

theorem fz1_116_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨128, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 128 (by decide)))

theorem fz1_116_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨129, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 129 (by decide)))

theorem fz1_116_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨130, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 130 (by decide)))

theorem fz1_116_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨131, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 131 (by decide)))

theorem fz1_116_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨132, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 132 (by decide)))

theorem fz1_116_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨133, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 133 (by decide)))

theorem fz1_116_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨134, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 134 (by decide)))

theorem fz1_116_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨135, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 135 (by decide)))

theorem fz1_116_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨136, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 136 (by decide)))

theorem fz1_116_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨137, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 137 (by decide)))

theorem fz1_116_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨138, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 138 (by decide)))

theorem fz1_116_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨139, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 139 (by decide)))

theorem fz1_116_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨140, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 140 (by decide)))

theorem fz1_116_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨141, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 141 (by decide)))

theorem fz1_116_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨142, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 142 (by decide)))

theorem fz1_116_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨143, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 143 (by decide)))

theorem fz1_116_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨144, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 144 (by decide)))

theorem fz1_116_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨145, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 145 (by decide)))

theorem fz1_116_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK116)) = 0 :=
  repsFixedCard rK116 ⟨146, by decide⟩ R116 hpxR116 hcardq116
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_116) 146 (by decide)))

theorem fixz2_116 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 54, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 84, 85, 86, 87, 88, 89, 91, 92, 93, 94, 96, 97, 98, 99, 101, 102, 103, 104, 106, 107, 108, 109, 111, 112, 113, 114, 115, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK116) (retConj 2 (Q2.R116_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_116_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨2, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 2 (by decide)))

theorem fz2_116_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨3, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 3 (by decide)))

theorem fz2_116_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨4, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 4 (by decide)))

theorem fz2_116_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨5, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 5 (by decide)))

theorem fz2_116_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨11, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 11 (by decide)))

theorem fz2_116_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨14, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 14 (by decide)))

theorem fz2_116_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨15, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 15 (by decide)))

theorem fz2_116_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨16, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 16 (by decide)))

theorem fz2_116_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨17, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 17 (by decide)))

theorem fz2_116_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨18, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 18 (by decide)))

theorem fz2_116_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨20, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 20 (by decide)))

theorem fz2_116_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨21, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 21 (by decide)))

theorem fz2_116_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨22, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 22 (by decide)))

theorem fz2_116_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨23, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 23 (by decide)))

theorem fz2_116_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨29, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 29 (by decide)))

theorem fz2_116_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨30, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 30 (by decide)))

theorem fz2_116_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨31, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 31 (by decide)))

theorem fz2_116_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨32, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 32 (by decide)))

theorem fz2_116_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨34, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 34 (by decide)))

theorem fz2_116_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨35, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 35 (by decide)))

theorem fz2_116_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨36, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 36 (by decide)))

theorem fz2_116_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨37, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 37 (by decide)))

theorem fz2_116_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨39, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 39 (by decide)))

theorem fz2_116_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨40, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 40 (by decide)))

theorem fz2_116_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨41, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 41 (by decide)))

theorem fz2_116_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨42, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 42 (by decide)))

theorem fz2_116_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨44, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 44 (by decide)))

theorem fz2_116_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨45, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 45 (by decide)))

theorem fz2_116_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨46, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 46 (by decide)))

theorem fz2_116_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨47, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 47 (by decide)))

theorem fz2_116_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨49, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 49 (by decide)))

theorem fz2_116_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨50, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 50 (by decide)))

theorem fz2_116_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨51, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 51 (by decide)))

theorem fz2_116_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨52, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 52 (by decide)))

theorem fz2_116_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨54, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 54 (by decide)))

theorem fz2_116_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨60, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 60 (by decide)))

theorem fz2_116_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨61, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 61 (by decide)))

theorem fz2_116_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨62, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 62 (by decide)))

theorem fz2_116_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨63, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 63 (by decide)))

theorem fz2_116_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨64, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 64 (by decide)))

theorem fz2_116_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨65, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 65 (by decide)))

theorem fz2_116_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨66, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 66 (by decide)))

theorem fz2_116_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨67, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 67 (by decide)))

theorem fz2_116_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨68, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 68 (by decide)))

theorem fz2_116_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨69, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 69 (by decide)))

theorem fz2_116_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨70, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 70 (by decide)))

theorem fz2_116_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨71, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 71 (by decide)))

theorem fz2_116_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨72, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 72 (by decide)))

theorem fz2_116_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨73, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 73 (by decide)))

theorem fz2_116_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨74, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 74 (by decide)))

theorem fz2_116_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨75, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 75 (by decide)))

theorem fz2_116_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨76, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 76 (by decide)))

theorem fz2_116_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨77, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 77 (by decide)))

theorem fz2_116_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨78, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 78 (by decide)))

theorem fz2_116_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨79, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 79 (by decide)))

theorem fz2_116_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨81, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 81 (by decide)))

theorem fz2_116_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨82, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 82 (by decide)))

theorem fz2_116_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨83, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 83 (by decide)))

theorem fz2_116_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨84, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 84 (by decide)))

theorem fz2_116_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨85, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 85 (by decide)))

theorem fz2_116_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨86, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 86 (by decide)))

theorem fz2_116_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨87, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 87 (by decide)))

theorem fz2_116_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨88, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 88 (by decide)))

theorem fz2_116_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨89, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 89 (by decide)))

theorem fz2_116_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨91, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 91 (by decide)))

theorem fz2_116_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨92, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 92 (by decide)))

theorem fz2_116_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨93, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 93 (by decide)))

theorem fz2_116_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨94, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 94 (by decide)))

theorem fz2_116_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨96, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 96 (by decide)))

theorem fz2_116_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨97, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 97 (by decide)))

theorem fz2_116_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨98, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 98 (by decide)))

theorem fz2_116_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨99, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 99 (by decide)))

theorem fz2_116_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨101, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 101 (by decide)))

theorem fz2_116_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨102, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 102 (by decide)))

theorem fz2_116_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨103, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 103 (by decide)))

theorem fz2_116_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨104, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 104 (by decide)))

theorem fz2_116_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨106, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 106 (by decide)))

theorem fz2_116_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨107, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 107 (by decide)))

theorem fz2_116_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨108, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 108 (by decide)))

theorem fz2_116_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨109, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 109 (by decide)))

theorem fz2_116_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨111, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 111 (by decide)))

theorem fz2_116_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨112, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 112 (by decide)))

theorem fz2_116_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨113, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 113 (by decide)))

theorem fz2_116_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨114, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 114 (by decide)))

theorem fz2_116_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨115, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 115 (by decide)))

theorem fz2_116_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨117, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 117 (by decide)))

theorem fz2_116_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨118, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 118 (by decide)))

theorem fz2_116_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨119, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 119 (by decide)))

theorem fz2_116_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨120, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 120 (by decide)))

theorem fz2_116_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨121, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 121 (by decide)))

theorem fz2_116_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨122, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 122 (by decide)))

theorem fz2_116_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨123, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 123 (by decide)))

theorem fz2_116_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨124, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 124 (by decide)))

theorem fz2_116_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨125, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 125 (by decide)))

theorem fz2_116_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨126, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 126 (by decide)))

theorem fz2_116_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨127, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 127 (by decide)))

theorem fz2_116_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨128, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 128 (by decide)))

theorem fz2_116_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨129, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 129 (by decide)))

theorem fz2_116_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨130, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 130 (by decide)))

theorem fz2_116_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨131, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 131 (by decide)))

theorem fz2_116_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨132, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 132 (by decide)))

theorem fz2_116_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨133, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 133 (by decide)))

theorem fz2_116_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨134, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 134 (by decide)))

theorem fz2_116_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨135, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 135 (by decide)))

theorem fz2_116_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨136, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 136 (by decide)))

theorem fz2_116_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨137, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 137 (by decide)))

theorem fz2_116_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨138, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 138 (by decide)))

theorem fz2_116_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨139, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 139 (by decide)))

theorem fz2_116_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨140, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 140 (by decide)))

theorem fz2_116_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨141, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 141 (by decide)))

theorem fz2_116_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨142, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 142 (by decide)))

theorem fz2_116_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨143, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 143 (by decide)))

theorem fz2_116_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨144, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 144 (by decide)))

theorem fz2_116_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨145, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 145 (by decide)))

theorem fz2_116_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK116)) = 0 :=
  Q2.repsFixedCard2 rK116 ⟨146, by decide⟩ Q2.R116_2 Q2.hpxR116_2 Q2.hcardq116_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_116) 146 (by decide)))

theorem fixz1_117 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 97, 98, 99, 100, 102, 103, 104, 105, 107, 108, 109, 110, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK117) (retConj 1 (R117 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_117_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨2, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 2 (by decide)))

theorem fz1_117_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨3, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 3 (by decide)))

theorem fz1_117_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨4, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 4 (by decide)))

theorem fz1_117_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨5, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 5 (by decide)))

theorem fz1_117_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨11, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 11 (by decide)))

theorem fz1_117_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨14, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 14 (by decide)))

theorem fz1_117_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨15, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 15 (by decide)))

theorem fz1_117_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨16, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 16 (by decide)))

theorem fz1_117_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨17, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 17 (by decide)))

theorem fz1_117_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨18, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 18 (by decide)))

theorem fz1_117_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨20, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 20 (by decide)))

theorem fz1_117_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨21, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 21 (by decide)))

theorem fz1_117_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨22, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 22 (by decide)))

theorem fz1_117_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨23, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 23 (by decide)))

theorem fz1_117_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨28, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 28 (by decide)))

theorem fz1_117_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨30, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 30 (by decide)))

theorem fz1_117_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨31, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 31 (by decide)))

theorem fz1_117_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨32, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 32 (by decide)))

theorem fz1_117_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨33, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 33 (by decide)))

theorem fz1_117_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨35, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 35 (by decide)))

theorem fz1_117_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨36, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 36 (by decide)))

theorem fz1_117_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨37, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 37 (by decide)))

theorem fz1_117_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨38, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 38 (by decide)))

theorem fz1_117_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨40, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 40 (by decide)))

theorem fz1_117_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨41, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 41 (by decide)))

theorem fz1_117_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨42, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 42 (by decide)))

theorem fz1_117_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨43, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 43 (by decide)))

theorem fz1_117_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨45, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 45 (by decide)))

theorem fz1_117_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨46, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 46 (by decide)))

theorem fz1_117_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨47, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 47 (by decide)))

theorem fz1_117_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨48, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 48 (by decide)))

theorem fz1_117_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨50, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 50 (by decide)))

theorem fz1_117_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨51, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 51 (by decide)))

theorem fz1_117_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨52, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 52 (by decide)))

theorem fz1_117_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨54, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 54 (by decide)))

theorem fz1_117_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨55, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 55 (by decide)))

theorem fz1_117_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨56, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 56 (by decide)))

theorem fz1_117_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨57, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 57 (by decide)))

theorem fz1_117_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨58, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 58 (by decide)))

theorem fz1_117_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨59, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 59 (by decide)))

theorem fz1_117_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨65, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 65 (by decide)))

theorem fz1_117_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨66, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 66 (by decide)))

theorem fz1_117_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨67, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 67 (by decide)))

theorem fz1_117_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨68, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 68 (by decide)))

theorem fz1_117_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨69, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 69 (by decide)))

theorem fz1_117_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨70, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 70 (by decide)))

theorem fz1_117_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨71, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 71 (by decide)))

theorem fz1_117_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨72, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 72 (by decide)))

theorem fz1_117_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨73, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 73 (by decide)))

theorem fz1_117_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨74, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 74 (by decide)))

theorem fz1_117_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨75, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 75 (by decide)))

theorem fz1_117_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨76, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 76 (by decide)))

theorem fz1_117_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨77, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 77 (by decide)))

theorem fz1_117_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨78, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 78 (by decide)))

theorem fz1_117_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨79, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 79 (by decide)))

theorem fz1_117_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨81, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 81 (by decide)))

theorem fz1_117_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨82, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 82 (by decide)))

theorem fz1_117_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨83, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 83 (by decide)))

theorem fz1_117_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨84, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 84 (by decide)))

theorem fz1_117_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨85, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 85 (by decide)))

theorem fz1_117_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨86, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 86 (by decide)))

theorem fz1_117_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨87, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 87 (by decide)))

theorem fz1_117_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨88, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 88 (by decide)))

theorem fz1_117_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨89, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 89 (by decide)))

theorem fz1_117_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨90, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 90 (by decide)))

theorem fz1_117_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨92, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 92 (by decide)))

theorem fz1_117_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨93, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 93 (by decide)))

theorem fz1_117_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨94, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 94 (by decide)))

theorem fz1_117_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨95, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 95 (by decide)))

theorem fz1_117_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨97, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 97 (by decide)))

theorem fz1_117_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨98, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 98 (by decide)))

theorem fz1_117_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨99, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 99 (by decide)))

theorem fz1_117_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨100, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 100 (by decide)))

theorem fz1_117_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨102, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 102 (by decide)))

theorem fz1_117_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨103, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 103 (by decide)))

theorem fz1_117_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨104, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 104 (by decide)))

theorem fz1_117_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨105, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 105 (by decide)))

theorem fz1_117_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨107, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 107 (by decide)))

theorem fz1_117_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨108, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 108 (by decide)))

theorem fz1_117_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨109, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 109 (by decide)))

theorem fz1_117_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨110, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 110 (by decide)))

theorem fz1_117_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨112, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 112 (by decide)))

theorem fz1_117_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨113, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 113 (by decide)))

theorem fz1_117_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨114, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 114 (by decide)))

theorem fz1_117_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨115, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 115 (by decide)))

theorem fz1_117_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨116, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 116 (by decide)))

theorem fz1_117_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨118, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 118 (by decide)))

theorem fz1_117_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨119, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 119 (by decide)))

theorem fz1_117_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨120, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 120 (by decide)))

theorem fz1_117_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨121, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 121 (by decide)))

theorem fz1_117_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨122, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 122 (by decide)))

theorem fz1_117_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨123, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 123 (by decide)))

theorem fz1_117_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨124, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 124 (by decide)))

theorem fz1_117_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨125, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 125 (by decide)))

theorem fz1_117_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨126, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 126 (by decide)))

theorem fz1_117_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨127, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 127 (by decide)))

theorem fz1_117_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨128, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 128 (by decide)))

theorem fz1_117_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨129, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 129 (by decide)))

theorem fz1_117_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨130, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 130 (by decide)))

theorem fz1_117_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨131, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 131 (by decide)))

theorem fz1_117_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨132, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 132 (by decide)))

theorem fz1_117_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨133, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 133 (by decide)))

theorem fz1_117_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨134, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 134 (by decide)))

theorem fz1_117_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨135, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 135 (by decide)))

theorem fz1_117_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨136, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 136 (by decide)))

theorem fz1_117_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨137, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 137 (by decide)))

theorem fz1_117_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨138, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 138 (by decide)))

theorem fz1_117_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨139, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 139 (by decide)))

theorem fz1_117_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨140, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 140 (by decide)))

theorem fz1_117_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨141, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 141 (by decide)))

theorem fz1_117_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨142, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 142 (by decide)))

theorem fz1_117_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨143, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 143 (by decide)))

theorem fz1_117_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨144, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 144 (by decide)))

theorem fz1_117_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨145, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 145 (by decide)))

theorem fz1_117_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK117)) = 0 :=
  repsFixedCard rK117 ⟨146, by decide⟩ R117 hpxR117 hcardq117
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_117) 146 (by decide)))

theorem fixz2_117 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 97, 98, 99, 100, 102, 103, 104, 105, 107, 108, 109, 110, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK117) (retConj 2 (Q2.R117_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_117_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨2, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 2 (by decide)))

theorem fz2_117_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨3, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 3 (by decide)))

theorem fz2_117_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨4, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 4 (by decide)))

theorem fz2_117_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨5, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 5 (by decide)))

theorem fz2_117_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨11, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 11 (by decide)))

theorem fz2_117_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨14, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 14 (by decide)))

theorem fz2_117_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨15, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 15 (by decide)))

theorem fz2_117_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨16, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 16 (by decide)))

theorem fz2_117_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨17, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 17 (by decide)))

theorem fz2_117_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨18, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 18 (by decide)))

theorem fz2_117_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨20, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 20 (by decide)))

theorem fz2_117_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨21, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 21 (by decide)))

theorem fz2_117_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨22, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 22 (by decide)))

theorem fz2_117_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨23, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 23 (by decide)))

theorem fz2_117_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨28, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 28 (by decide)))

theorem fz2_117_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨30, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 30 (by decide)))

theorem fz2_117_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨31, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 31 (by decide)))

theorem fz2_117_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨32, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 32 (by decide)))

theorem fz2_117_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨33, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 33 (by decide)))

theorem fz2_117_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨35, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 35 (by decide)))

theorem fz2_117_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨36, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 36 (by decide)))

theorem fz2_117_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨37, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 37 (by decide)))

theorem fz2_117_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨38, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 38 (by decide)))

theorem fz2_117_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨40, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 40 (by decide)))

theorem fz2_117_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨41, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 41 (by decide)))

theorem fz2_117_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨42, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 42 (by decide)))

theorem fz2_117_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨43, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 43 (by decide)))

theorem fz2_117_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨45, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 45 (by decide)))

theorem fz2_117_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨46, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 46 (by decide)))

theorem fz2_117_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨47, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 47 (by decide)))

theorem fz2_117_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨48, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 48 (by decide)))

theorem fz2_117_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨50, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 50 (by decide)))

theorem fz2_117_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨51, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 51 (by decide)))

theorem fz2_117_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨52, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 52 (by decide)))

theorem fz2_117_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨54, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 54 (by decide)))

theorem fz2_117_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨55, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 55 (by decide)))

theorem fz2_117_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨56, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 56 (by decide)))

theorem fz2_117_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨57, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 57 (by decide)))

theorem fz2_117_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨58, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 58 (by decide)))

theorem fz2_117_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨59, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 59 (by decide)))

theorem fz2_117_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨65, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 65 (by decide)))

theorem fz2_117_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨66, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 66 (by decide)))

theorem fz2_117_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨67, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 67 (by decide)))

theorem fz2_117_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨68, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 68 (by decide)))

theorem fz2_117_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨69, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 69 (by decide)))

theorem fz2_117_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨70, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 70 (by decide)))

theorem fz2_117_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨71, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 71 (by decide)))

theorem fz2_117_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨72, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 72 (by decide)))

theorem fz2_117_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨73, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 73 (by decide)))

theorem fz2_117_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨74, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 74 (by decide)))

theorem fz2_117_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨75, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 75 (by decide)))

theorem fz2_117_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨76, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 76 (by decide)))

theorem fz2_117_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨77, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 77 (by decide)))

theorem fz2_117_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨78, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 78 (by decide)))

theorem fz2_117_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨79, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 79 (by decide)))

theorem fz2_117_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨81, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 81 (by decide)))

theorem fz2_117_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨82, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 82 (by decide)))

theorem fz2_117_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨83, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 83 (by decide)))

theorem fz2_117_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨84, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 84 (by decide)))

theorem fz2_117_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨85, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 85 (by decide)))

theorem fz2_117_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨86, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 86 (by decide)))

theorem fz2_117_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨87, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 87 (by decide)))

theorem fz2_117_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨88, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 88 (by decide)))

theorem fz2_117_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨89, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 89 (by decide)))

theorem fz2_117_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨90, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 90 (by decide)))

theorem fz2_117_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨92, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 92 (by decide)))

theorem fz2_117_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨93, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 93 (by decide)))

theorem fz2_117_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨94, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 94 (by decide)))

theorem fz2_117_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨95, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 95 (by decide)))

theorem fz2_117_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨97, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 97 (by decide)))

theorem fz2_117_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨98, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 98 (by decide)))

theorem fz2_117_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨99, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 99 (by decide)))

theorem fz2_117_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨100, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 100 (by decide)))

theorem fz2_117_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨102, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 102 (by decide)))

theorem fz2_117_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨103, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 103 (by decide)))

theorem fz2_117_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨104, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 104 (by decide)))

theorem fz2_117_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨105, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 105 (by decide)))

theorem fz2_117_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨107, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 107 (by decide)))

theorem fz2_117_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨108, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 108 (by decide)))

theorem fz2_117_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨109, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 109 (by decide)))

theorem fz2_117_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨110, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 110 (by decide)))

theorem fz2_117_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨112, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 112 (by decide)))

theorem fz2_117_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨113, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 113 (by decide)))

theorem fz2_117_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨114, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 114 (by decide)))

theorem fz2_117_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨115, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 115 (by decide)))

theorem fz2_117_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨116, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 116 (by decide)))

theorem fz2_117_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨118, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 118 (by decide)))

theorem fz2_117_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨119, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 119 (by decide)))

theorem fz2_117_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨120, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 120 (by decide)))

theorem fz2_117_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨121, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 121 (by decide)))

theorem fz2_117_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨122, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 122 (by decide)))

theorem fz2_117_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨123, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 123 (by decide)))

theorem fz2_117_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨124, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 124 (by decide)))

theorem fz2_117_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨125, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 125 (by decide)))

theorem fz2_117_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨126, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 126 (by decide)))

theorem fz2_117_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨127, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 127 (by decide)))

theorem fz2_117_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨128, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 128 (by decide)))

theorem fz2_117_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨129, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 129 (by decide)))

theorem fz2_117_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨130, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 130 (by decide)))

theorem fz2_117_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨131, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 131 (by decide)))

theorem fz2_117_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨132, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 132 (by decide)))

theorem fz2_117_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨133, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 133 (by decide)))

theorem fz2_117_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨134, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 134 (by decide)))

theorem fz2_117_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨135, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 135 (by decide)))

theorem fz2_117_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨136, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 136 (by decide)))

theorem fz2_117_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨137, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 137 (by decide)))

theorem fz2_117_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨138, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 138 (by decide)))

theorem fz2_117_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨139, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 139 (by decide)))

theorem fz2_117_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨140, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 140 (by decide)))

theorem fz2_117_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨141, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 141 (by decide)))

theorem fz2_117_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨142, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 142 (by decide)))

theorem fz2_117_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨143, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 143 (by decide)))

theorem fz2_117_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨144, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 144 (by decide)))

theorem fz2_117_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨145, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 145 (by decide)))

theorem fz2_117_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK117)) = 0 :=
  Q2.repsFixedCard2 rK117 ⟨146, by decide⟩ Q2.R117_2 Q2.hpxR117_2 Q2.hcardq117_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_117) 146 (by decide)))

theorem fixz1_118 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 93, 94, 95, 96, 98, 99, 100, 101, 103, 104, 105, 106, 108, 109, 110, 111, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK118) (retConj 1 (R118 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_118_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨2, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 2 (by decide)))

theorem fz1_118_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨3, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 3 (by decide)))

theorem fz1_118_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨4, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 4 (by decide)))

theorem fz1_118_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨5, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 5 (by decide)))

theorem fz1_118_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨11, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 11 (by decide)))

theorem fz1_118_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨14, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 14 (by decide)))

theorem fz1_118_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨15, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 15 (by decide)))

theorem fz1_118_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨16, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 16 (by decide)))

theorem fz1_118_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨17, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 17 (by decide)))

theorem fz1_118_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨18, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 18 (by decide)))

theorem fz1_118_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨20, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 20 (by decide)))

theorem fz1_118_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨21, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 21 (by decide)))

theorem fz1_118_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨22, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 22 (by decide)))

theorem fz1_118_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨23, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 23 (by decide)))

theorem fz1_118_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨28, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 28 (by decide)))

theorem fz1_118_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨29, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 29 (by decide)))

theorem fz1_118_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨31, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 31 (by decide)))

theorem fz1_118_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨32, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 32 (by decide)))

theorem fz1_118_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨33, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 33 (by decide)))

theorem fz1_118_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨34, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 34 (by decide)))

theorem fz1_118_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨36, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 36 (by decide)))

theorem fz1_118_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨37, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 37 (by decide)))

theorem fz1_118_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨38, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 38 (by decide)))

theorem fz1_118_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨39, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 39 (by decide)))

theorem fz1_118_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨41, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 41 (by decide)))

theorem fz1_118_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨42, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 42 (by decide)))

theorem fz1_118_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨43, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 43 (by decide)))

theorem fz1_118_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨44, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 44 (by decide)))

theorem fz1_118_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨46, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 46 (by decide)))

theorem fz1_118_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨47, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 47 (by decide)))

theorem fz1_118_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨48, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 48 (by decide)))

theorem fz1_118_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨49, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 49 (by decide)))

theorem fz1_118_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨51, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 51 (by decide)))

theorem fz1_118_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨52, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 52 (by decide)))

theorem fz1_118_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨54, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 54 (by decide)))

theorem fz1_118_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨55, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 55 (by decide)))

theorem fz1_118_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨56, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 56 (by decide)))

theorem fz1_118_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨57, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 57 (by decide)))

theorem fz1_118_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨58, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 58 (by decide)))

theorem fz1_118_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨59, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 59 (by decide)))

theorem fz1_118_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨60, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 60 (by decide)))

theorem fz1_118_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨61, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 61 (by decide)))

theorem fz1_118_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨62, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 62 (by decide)))

theorem fz1_118_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨63, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 63 (by decide)))

theorem fz1_118_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨64, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 64 (by decide)))

theorem fz1_118_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨70, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 70 (by decide)))

theorem fz1_118_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨71, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 71 (by decide)))

theorem fz1_118_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨72, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 72 (by decide)))

theorem fz1_118_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨73, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 73 (by decide)))

theorem fz1_118_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨74, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 74 (by decide)))

theorem fz1_118_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨75, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 75 (by decide)))

theorem fz1_118_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨76, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 76 (by decide)))

theorem fz1_118_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨77, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 77 (by decide)))

theorem fz1_118_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨78, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 78 (by decide)))

theorem fz1_118_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨79, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 79 (by decide)))

theorem fz1_118_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨81, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 81 (by decide)))

theorem fz1_118_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨82, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 82 (by decide)))

theorem fz1_118_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨83, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 83 (by decide)))

theorem fz1_118_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨84, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 84 (by decide)))

theorem fz1_118_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨85, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 85 (by decide)))

theorem fz1_118_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨86, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 86 (by decide)))

theorem fz1_118_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨87, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 87 (by decide)))

theorem fz1_118_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨88, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 88 (by decide)))

theorem fz1_118_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨89, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 89 (by decide)))

theorem fz1_118_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨90, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 90 (by decide)))

theorem fz1_118_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨91, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 91 (by decide)))

theorem fz1_118_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨93, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 93 (by decide)))

theorem fz1_118_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨94, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 94 (by decide)))

theorem fz1_118_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨95, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 95 (by decide)))

theorem fz1_118_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨96, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 96 (by decide)))

theorem fz1_118_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨98, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 98 (by decide)))

theorem fz1_118_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨99, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 99 (by decide)))

theorem fz1_118_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨100, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 100 (by decide)))

theorem fz1_118_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨101, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 101 (by decide)))

theorem fz1_118_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨103, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 103 (by decide)))

theorem fz1_118_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨104, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 104 (by decide)))

theorem fz1_118_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨105, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 105 (by decide)))

theorem fz1_118_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨106, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 106 (by decide)))

theorem fz1_118_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨108, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 108 (by decide)))

theorem fz1_118_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨109, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 109 (by decide)))

theorem fz1_118_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨110, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 110 (by decide)))

theorem fz1_118_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨111, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 111 (by decide)))

theorem fz1_118_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨113, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 113 (by decide)))

theorem fz1_118_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨114, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 114 (by decide)))

theorem fz1_118_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨115, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 115 (by decide)))

theorem fz1_118_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨116, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 116 (by decide)))

theorem fz1_118_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨117, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 117 (by decide)))

theorem fz1_118_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨119, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 119 (by decide)))

theorem fz1_118_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨120, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 120 (by decide)))

theorem fz1_118_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨121, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 121 (by decide)))

theorem fz1_118_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨122, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 122 (by decide)))

theorem fz1_118_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨123, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 123 (by decide)))

theorem fz1_118_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨124, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 124 (by decide)))

theorem fz1_118_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨125, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 125 (by decide)))

theorem fz1_118_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨126, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 126 (by decide)))

theorem fz1_118_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨127, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 127 (by decide)))

theorem fz1_118_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨128, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 128 (by decide)))

theorem fz1_118_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨129, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 129 (by decide)))

theorem fz1_118_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨130, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 130 (by decide)))

theorem fz1_118_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨131, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 131 (by decide)))

theorem fz1_118_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨132, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 132 (by decide)))

theorem fz1_118_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨133, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 133 (by decide)))

theorem fz1_118_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨134, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 134 (by decide)))

theorem fz1_118_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨135, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 135 (by decide)))

theorem fz1_118_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨136, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 136 (by decide)))

theorem fz1_118_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨137, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 137 (by decide)))

theorem fz1_118_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨138, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 138 (by decide)))

theorem fz1_118_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨139, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 139 (by decide)))

theorem fz1_118_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨140, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 140 (by decide)))

theorem fz1_118_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨141, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 141 (by decide)))

theorem fz1_118_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨142, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 142 (by decide)))

theorem fz1_118_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨143, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 143 (by decide)))

theorem fz1_118_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨144, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 144 (by decide)))

theorem fz1_118_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨145, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 145 (by decide)))

theorem fz1_118_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK118)) = 0 :=
  repsFixedCard rK118 ⟨146, by decide⟩ R118 hpxR118 hcardq118
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_118) 146 (by decide)))

theorem fixz2_118 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 93, 94, 95, 96, 98, 99, 100, 101, 103, 104, 105, 106, 108, 109, 110, 111, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK118) (retConj 2 (Q2.R118_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_118_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨2, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 2 (by decide)))

theorem fz2_118_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨3, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 3 (by decide)))

theorem fz2_118_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨4, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 4 (by decide)))

theorem fz2_118_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨5, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 5 (by decide)))

theorem fz2_118_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨11, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 11 (by decide)))

theorem fz2_118_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨14, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 14 (by decide)))

theorem fz2_118_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨15, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 15 (by decide)))

theorem fz2_118_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨16, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 16 (by decide)))

theorem fz2_118_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨17, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 17 (by decide)))

theorem fz2_118_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨18, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 18 (by decide)))

theorem fz2_118_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨20, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 20 (by decide)))

theorem fz2_118_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨21, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 21 (by decide)))

theorem fz2_118_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨22, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 22 (by decide)))

theorem fz2_118_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨23, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 23 (by decide)))

theorem fz2_118_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨28, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 28 (by decide)))

theorem fz2_118_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨29, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 29 (by decide)))

theorem fz2_118_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨31, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 31 (by decide)))

theorem fz2_118_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨32, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 32 (by decide)))

theorem fz2_118_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨33, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 33 (by decide)))

theorem fz2_118_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨34, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 34 (by decide)))

theorem fz2_118_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨36, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 36 (by decide)))

theorem fz2_118_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨37, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 37 (by decide)))

theorem fz2_118_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨38, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 38 (by decide)))

theorem fz2_118_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨39, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 39 (by decide)))

theorem fz2_118_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨41, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 41 (by decide)))

theorem fz2_118_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨42, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 42 (by decide)))

theorem fz2_118_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨43, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 43 (by decide)))

theorem fz2_118_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨44, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 44 (by decide)))

theorem fz2_118_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨46, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 46 (by decide)))

theorem fz2_118_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨47, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 47 (by decide)))

theorem fz2_118_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨48, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 48 (by decide)))

theorem fz2_118_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨49, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 49 (by decide)))

theorem fz2_118_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨51, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 51 (by decide)))

theorem fz2_118_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨52, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 52 (by decide)))

theorem fz2_118_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨54, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 54 (by decide)))

theorem fz2_118_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨55, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 55 (by decide)))

theorem fz2_118_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨56, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 56 (by decide)))

theorem fz2_118_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨57, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 57 (by decide)))

theorem fz2_118_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨58, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 58 (by decide)))

theorem fz2_118_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨59, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 59 (by decide)))

theorem fz2_118_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨60, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 60 (by decide)))

theorem fz2_118_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨61, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 61 (by decide)))

theorem fz2_118_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨62, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 62 (by decide)))

theorem fz2_118_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨63, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 63 (by decide)))

theorem fz2_118_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨64, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 64 (by decide)))

theorem fz2_118_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨70, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 70 (by decide)))

theorem fz2_118_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨71, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 71 (by decide)))

theorem fz2_118_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨72, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 72 (by decide)))

theorem fz2_118_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨73, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 73 (by decide)))

theorem fz2_118_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨74, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 74 (by decide)))

theorem fz2_118_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨75, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 75 (by decide)))

theorem fz2_118_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨76, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 76 (by decide)))

theorem fz2_118_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨77, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 77 (by decide)))

theorem fz2_118_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨78, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 78 (by decide)))

theorem fz2_118_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨79, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 79 (by decide)))

theorem fz2_118_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨81, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 81 (by decide)))

theorem fz2_118_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨82, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 82 (by decide)))

theorem fz2_118_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨83, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 83 (by decide)))

theorem fz2_118_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨84, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 84 (by decide)))

theorem fz2_118_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨85, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 85 (by decide)))

theorem fz2_118_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨86, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 86 (by decide)))

theorem fz2_118_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨87, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 87 (by decide)))

theorem fz2_118_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨88, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 88 (by decide)))

theorem fz2_118_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨89, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 89 (by decide)))

theorem fz2_118_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨90, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 90 (by decide)))

theorem fz2_118_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨91, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 91 (by decide)))

theorem fz2_118_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨93, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 93 (by decide)))

theorem fz2_118_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨94, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 94 (by decide)))

theorem fz2_118_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨95, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 95 (by decide)))

theorem fz2_118_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨96, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 96 (by decide)))

theorem fz2_118_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨98, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 98 (by decide)))

theorem fz2_118_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨99, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 99 (by decide)))

theorem fz2_118_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨100, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 100 (by decide)))

theorem fz2_118_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨101, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 101 (by decide)))

theorem fz2_118_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨103, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 103 (by decide)))

theorem fz2_118_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨104, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 104 (by decide)))

theorem fz2_118_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨105, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 105 (by decide)))

theorem fz2_118_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨106, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 106 (by decide)))

theorem fz2_118_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨108, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 108 (by decide)))

theorem fz2_118_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨109, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 109 (by decide)))

theorem fz2_118_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨110, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 110 (by decide)))

theorem fz2_118_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨111, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 111 (by decide)))

theorem fz2_118_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨113, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 113 (by decide)))

theorem fz2_118_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨114, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 114 (by decide)))

theorem fz2_118_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨115, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 115 (by decide)))

theorem fz2_118_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨116, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 116 (by decide)))

theorem fz2_118_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨117, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 117 (by decide)))

theorem fz2_118_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨119, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 119 (by decide)))

theorem fz2_118_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨120, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 120 (by decide)))

theorem fz2_118_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨121, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 121 (by decide)))

theorem fz2_118_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨122, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 122 (by decide)))

theorem fz2_118_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨123, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 123 (by decide)))

theorem fz2_118_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨124, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 124 (by decide)))

theorem fz2_118_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨125, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 125 (by decide)))

theorem fz2_118_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨126, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 126 (by decide)))

theorem fz2_118_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨127, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 127 (by decide)))

theorem fz2_118_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨128, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 128 (by decide)))

theorem fz2_118_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨129, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 129 (by decide)))

theorem fz2_118_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨130, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 130 (by decide)))

theorem fz2_118_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨131, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 131 (by decide)))

theorem fz2_118_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨132, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 132 (by decide)))

theorem fz2_118_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨133, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 133 (by decide)))

theorem fz2_118_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨134, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 134 (by decide)))

theorem fz2_118_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨135, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 135 (by decide)))

theorem fz2_118_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨136, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 136 (by decide)))

theorem fz2_118_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨137, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 137 (by decide)))

theorem fz2_118_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨138, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 138 (by decide)))

theorem fz2_118_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨139, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 139 (by decide)))

theorem fz2_118_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨140, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 140 (by decide)))

theorem fz2_118_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨141, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 141 (by decide)))

theorem fz2_118_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨142, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 142 (by decide)))

theorem fz2_118_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨143, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 143 (by decide)))

theorem fz2_118_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨144, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 144 (by decide)))

theorem fz2_118_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨145, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 145 (by decide)))

theorem fz2_118_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK118)) = 0 :=
  Q2.repsFixedCard2 rK118 ⟨146, by decide⟩ Q2.R118_2 Q2.hpxR118_2 Q2.hcardq118_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_118) 146 (by decide)))

theorem fixz1_119 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 75, 76, 77, 78, 79, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 97, 99, 100, 101, 102, 104, 105, 106, 107, 109, 110, 111, 112, 114, 115, 116, 117, 118, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK119) (retConj 1 (R119 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_119_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨2, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 2 (by decide)))

theorem fz1_119_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨3, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 3 (by decide)))

theorem fz1_119_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨4, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 4 (by decide)))

theorem fz1_119_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨5, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 5 (by decide)))

theorem fz1_119_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨11, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 11 (by decide)))

theorem fz1_119_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨14, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 14 (by decide)))

theorem fz1_119_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨15, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 15 (by decide)))

theorem fz1_119_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨16, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 16 (by decide)))

theorem fz1_119_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨17, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 17 (by decide)))

theorem fz1_119_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨18, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 18 (by decide)))

theorem fz1_119_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨20, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 20 (by decide)))

theorem fz1_119_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨21, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 21 (by decide)))

theorem fz1_119_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨22, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 22 (by decide)))

theorem fz1_119_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨23, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 23 (by decide)))

theorem fz1_119_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨28, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 28 (by decide)))

theorem fz1_119_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨29, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 29 (by decide)))

theorem fz1_119_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨30, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 30 (by decide)))

theorem fz1_119_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨32, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 32 (by decide)))

theorem fz1_119_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨33, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 33 (by decide)))

theorem fz1_119_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨34, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 34 (by decide)))

theorem fz1_119_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨35, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 35 (by decide)))

theorem fz1_119_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨37, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 37 (by decide)))

theorem fz1_119_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨38, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 38 (by decide)))

theorem fz1_119_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨39, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 39 (by decide)))

theorem fz1_119_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨40, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 40 (by decide)))

theorem fz1_119_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨42, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 42 (by decide)))

theorem fz1_119_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨43, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 43 (by decide)))

theorem fz1_119_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨44, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 44 (by decide)))

theorem fz1_119_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨45, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 45 (by decide)))

theorem fz1_119_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨47, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 47 (by decide)))

theorem fz1_119_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨48, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 48 (by decide)))

theorem fz1_119_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨49, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 49 (by decide)))

theorem fz1_119_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨50, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 50 (by decide)))

theorem fz1_119_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨52, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 52 (by decide)))

theorem fz1_119_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨54, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 54 (by decide)))

theorem fz1_119_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨55, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 55 (by decide)))

theorem fz1_119_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨56, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 56 (by decide)))

theorem fz1_119_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨57, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 57 (by decide)))

theorem fz1_119_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨58, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 58 (by decide)))

theorem fz1_119_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨59, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 59 (by decide)))

theorem fz1_119_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨60, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 60 (by decide)))

theorem fz1_119_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨61, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 61 (by decide)))

theorem fz1_119_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨62, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 62 (by decide)))

theorem fz1_119_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨63, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 63 (by decide)))

theorem fz1_119_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨64, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 64 (by decide)))

theorem fz1_119_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨65, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 65 (by decide)))

theorem fz1_119_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨66, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 66 (by decide)))

theorem fz1_119_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨67, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 67 (by decide)))

theorem fz1_119_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨68, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 68 (by decide)))

theorem fz1_119_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨69, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 69 (by decide)))

theorem fz1_119_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨75, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 75 (by decide)))

theorem fz1_119_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨76, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 76 (by decide)))

theorem fz1_119_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨77, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 77 (by decide)))

theorem fz1_119_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨78, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 78 (by decide)))

theorem fz1_119_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨79, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 79 (by decide)))

theorem fz1_119_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨81, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 81 (by decide)))

theorem fz1_119_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨82, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 82 (by decide)))

theorem fz1_119_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨83, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 83 (by decide)))

theorem fz1_119_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨84, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 84 (by decide)))

theorem fz1_119_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨85, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 85 (by decide)))

theorem fz1_119_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨86, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 86 (by decide)))

theorem fz1_119_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨87, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 87 (by decide)))

theorem fz1_119_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨88, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 88 (by decide)))

theorem fz1_119_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨89, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 89 (by decide)))

theorem fz1_119_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨90, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 90 (by decide)))

theorem fz1_119_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨91, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 91 (by decide)))

theorem fz1_119_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨92, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 92 (by decide)))

theorem fz1_119_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨94, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 94 (by decide)))

theorem fz1_119_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨95, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 95 (by decide)))

theorem fz1_119_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨96, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 96 (by decide)))

theorem fz1_119_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨97, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 97 (by decide)))

theorem fz1_119_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨99, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 99 (by decide)))

theorem fz1_119_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨100, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 100 (by decide)))

theorem fz1_119_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨101, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 101 (by decide)))

theorem fz1_119_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨102, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 102 (by decide)))

theorem fz1_119_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨104, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 104 (by decide)))

theorem fz1_119_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨105, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 105 (by decide)))

theorem fz1_119_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨106, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 106 (by decide)))

theorem fz1_119_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨107, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 107 (by decide)))

theorem fz1_119_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨109, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 109 (by decide)))

theorem fz1_119_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨110, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 110 (by decide)))

theorem fz1_119_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨111, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 111 (by decide)))

theorem fz1_119_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨112, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 112 (by decide)))

theorem fz1_119_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨114, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 114 (by decide)))

theorem fz1_119_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨115, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 115 (by decide)))

theorem fz1_119_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨116, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 116 (by decide)))

theorem fz1_119_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨117, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 117 (by decide)))

theorem fz1_119_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨118, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 118 (by decide)))

theorem fz1_119_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨120, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 120 (by decide)))

theorem fz1_119_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨121, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 121 (by decide)))

theorem fz1_119_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨122, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 122 (by decide)))

theorem fz1_119_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨123, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 123 (by decide)))

theorem fz1_119_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨124, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 124 (by decide)))

theorem fz1_119_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨125, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 125 (by decide)))

theorem fz1_119_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨126, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 126 (by decide)))

theorem fz1_119_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨127, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 127 (by decide)))

theorem fz1_119_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨128, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 128 (by decide)))

theorem fz1_119_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨129, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 129 (by decide)))

theorem fz1_119_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨130, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 130 (by decide)))

theorem fz1_119_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨131, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 131 (by decide)))

theorem fz1_119_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨132, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 132 (by decide)))

theorem fz1_119_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨133, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 133 (by decide)))

theorem fz1_119_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨134, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 134 (by decide)))

theorem fz1_119_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨135, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 135 (by decide)))

theorem fz1_119_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨136, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 136 (by decide)))

theorem fz1_119_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨137, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 137 (by decide)))

theorem fz1_119_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨138, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 138 (by decide)))

theorem fz1_119_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨139, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 139 (by decide)))

theorem fz1_119_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨140, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 140 (by decide)))

theorem fz1_119_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨141, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 141 (by decide)))

theorem fz1_119_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨142, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 142 (by decide)))

theorem fz1_119_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨143, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 143 (by decide)))

theorem fz1_119_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨144, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 144 (by decide)))

theorem fz1_119_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨145, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 145 (by decide)))

theorem fz1_119_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK119)) = 0 :=
  repsFixedCard rK119 ⟨146, by decide⟩ R119 hpxR119 hcardq119
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_119) 146 (by decide)))

theorem fixz2_119 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 75, 76, 77, 78, 79, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 97, 99, 100, 101, 102, 104, 105, 106, 107, 109, 110, 111, 112, 114, 115, 116, 117, 118, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK119) (retConj 2 (Q2.R119_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_119_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨2, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 2 (by decide)))

theorem fz2_119_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨3, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 3 (by decide)))

theorem fz2_119_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨4, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 4 (by decide)))

theorem fz2_119_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨5, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 5 (by decide)))

theorem fz2_119_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨11, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 11 (by decide)))

theorem fz2_119_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨14, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 14 (by decide)))

theorem fz2_119_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨15, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 15 (by decide)))

theorem fz2_119_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨16, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 16 (by decide)))

theorem fz2_119_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨17, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 17 (by decide)))

theorem fz2_119_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨18, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 18 (by decide)))

theorem fz2_119_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨20, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 20 (by decide)))

theorem fz2_119_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨21, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 21 (by decide)))

theorem fz2_119_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨22, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 22 (by decide)))

theorem fz2_119_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨23, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 23 (by decide)))

theorem fz2_119_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨28, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 28 (by decide)))

theorem fz2_119_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨29, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 29 (by decide)))

theorem fz2_119_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨30, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 30 (by decide)))

theorem fz2_119_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨32, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 32 (by decide)))

theorem fz2_119_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨33, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 33 (by decide)))

theorem fz2_119_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨34, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 34 (by decide)))

theorem fz2_119_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨35, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 35 (by decide)))

theorem fz2_119_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨37, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 37 (by decide)))

theorem fz2_119_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨38, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 38 (by decide)))

theorem fz2_119_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨39, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 39 (by decide)))

theorem fz2_119_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨40, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 40 (by decide)))

theorem fz2_119_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨42, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 42 (by decide)))

theorem fz2_119_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨43, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 43 (by decide)))

theorem fz2_119_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨44, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 44 (by decide)))

theorem fz2_119_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨45, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 45 (by decide)))

theorem fz2_119_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨47, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 47 (by decide)))

theorem fz2_119_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨48, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 48 (by decide)))

theorem fz2_119_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨49, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 49 (by decide)))

theorem fz2_119_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨50, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 50 (by decide)))

theorem fz2_119_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨52, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 52 (by decide)))

theorem fz2_119_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨54, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 54 (by decide)))

theorem fz2_119_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨55, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 55 (by decide)))

theorem fz2_119_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨56, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 56 (by decide)))

theorem fz2_119_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨57, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 57 (by decide)))

theorem fz2_119_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨58, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 58 (by decide)))

theorem fz2_119_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨59, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 59 (by decide)))

theorem fz2_119_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨60, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 60 (by decide)))

theorem fz2_119_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨61, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 61 (by decide)))

theorem fz2_119_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨62, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 62 (by decide)))

theorem fz2_119_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨63, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 63 (by decide)))

theorem fz2_119_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨64, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 64 (by decide)))

theorem fz2_119_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨65, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 65 (by decide)))

theorem fz2_119_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨66, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 66 (by decide)))

theorem fz2_119_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨67, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 67 (by decide)))

theorem fz2_119_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨68, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 68 (by decide)))

theorem fz2_119_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨69, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 69 (by decide)))

theorem fz2_119_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨75, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 75 (by decide)))

theorem fz2_119_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨76, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 76 (by decide)))

theorem fz2_119_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨77, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 77 (by decide)))

theorem fz2_119_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨78, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 78 (by decide)))

theorem fz2_119_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨79, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 79 (by decide)))

theorem fz2_119_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨81, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 81 (by decide)))

theorem fz2_119_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨82, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 82 (by decide)))

theorem fz2_119_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨83, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 83 (by decide)))

theorem fz2_119_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨84, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 84 (by decide)))

theorem fz2_119_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨85, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 85 (by decide)))

theorem fz2_119_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨86, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 86 (by decide)))

theorem fz2_119_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨87, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 87 (by decide)))

theorem fz2_119_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨88, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 88 (by decide)))

theorem fz2_119_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨89, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 89 (by decide)))

theorem fz2_119_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨90, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 90 (by decide)))

theorem fz2_119_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨91, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 91 (by decide)))

theorem fz2_119_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨92, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 92 (by decide)))

theorem fz2_119_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨94, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 94 (by decide)))

theorem fz2_119_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨95, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 95 (by decide)))

theorem fz2_119_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨96, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 96 (by decide)))

theorem fz2_119_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨97, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 97 (by decide)))

theorem fz2_119_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨99, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 99 (by decide)))

theorem fz2_119_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨100, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 100 (by decide)))

theorem fz2_119_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨101, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 101 (by decide)))

theorem fz2_119_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨102, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 102 (by decide)))

theorem fz2_119_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨104, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 104 (by decide)))

theorem fz2_119_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨105, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 105 (by decide)))

theorem fz2_119_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨106, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 106 (by decide)))

theorem fz2_119_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨107, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 107 (by decide)))

theorem fz2_119_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨109, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 109 (by decide)))

theorem fz2_119_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨110, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 110 (by decide)))

theorem fz2_119_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨111, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 111 (by decide)))

theorem fz2_119_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨112, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 112 (by decide)))

theorem fz2_119_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨114, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 114 (by decide)))

theorem fz2_119_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨115, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 115 (by decide)))

theorem fz2_119_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨116, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 116 (by decide)))

theorem fz2_119_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨117, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 117 (by decide)))

theorem fz2_119_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨118, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 118 (by decide)))

theorem fz2_119_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨120, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 120 (by decide)))

theorem fz2_119_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨121, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 121 (by decide)))

theorem fz2_119_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨122, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 122 (by decide)))

theorem fz2_119_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨123, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 123 (by decide)))

theorem fz2_119_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨124, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 124 (by decide)))

theorem fz2_119_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨125, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 125 (by decide)))

theorem fz2_119_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨126, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 126 (by decide)))

theorem fz2_119_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨127, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 127 (by decide)))

theorem fz2_119_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨128, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 128 (by decide)))

theorem fz2_119_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨129, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 129 (by decide)))

theorem fz2_119_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨130, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 130 (by decide)))

theorem fz2_119_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨131, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 131 (by decide)))

theorem fz2_119_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨132, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 132 (by decide)))

theorem fz2_119_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨133, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 133 (by decide)))

theorem fz2_119_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨134, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 134 (by decide)))

theorem fz2_119_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨135, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 135 (by decide)))

theorem fz2_119_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨136, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 136 (by decide)))

theorem fz2_119_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨137, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 137 (by decide)))

theorem fz2_119_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨138, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 138 (by decide)))

theorem fz2_119_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨139, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 139 (by decide)))

theorem fz2_119_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨140, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 140 (by decide)))

theorem fz2_119_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨141, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 141 (by decide)))

theorem fz2_119_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨142, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 142 (by decide)))

theorem fz2_119_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨143, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 143 (by decide)))

theorem fz2_119_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨144, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 144 (by decide)))

theorem fz2_119_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨145, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 145 (by decide)))

theorem fz2_119_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK119)) = 0 :=
  Q2.repsFixedCard2 rK119 ⟨146, by decide⟩ Q2.R119_2 Q2.hpxR119_2 Q2.hcardq119_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_119) 146 (by decide)))

theorem fixz1_120 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 97, 98, 100, 101, 102, 103, 105, 106, 107, 108, 110, 111, 112, 113, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK120) (retConj 1 (R120 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_120_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨2, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 2 (by decide)))

theorem fz1_120_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨3, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 3 (by decide)))

theorem fz1_120_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨4, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 4 (by decide)))

theorem fz1_120_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨5, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 5 (by decide)))

theorem fz1_120_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨11, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 11 (by decide)))

theorem fz1_120_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨14, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 14 (by decide)))

theorem fz1_120_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨15, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 15 (by decide)))

theorem fz1_120_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨16, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 16 (by decide)))

theorem fz1_120_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨17, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 17 (by decide)))

theorem fz1_120_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨18, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 18 (by decide)))

theorem fz1_120_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨20, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 20 (by decide)))

theorem fz1_120_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨21, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 21 (by decide)))

theorem fz1_120_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨22, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 22 (by decide)))

theorem fz1_120_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨23, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 23 (by decide)))

theorem fz1_120_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨28, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 28 (by decide)))

theorem fz1_120_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨29, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 29 (by decide)))

theorem fz1_120_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨30, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 30 (by decide)))

theorem fz1_120_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨31, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 31 (by decide)))

theorem fz1_120_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨33, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 33 (by decide)))

theorem fz1_120_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨34, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 34 (by decide)))

theorem fz1_120_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨35, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 35 (by decide)))

theorem fz1_120_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨36, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 36 (by decide)))

theorem fz1_120_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨38, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 38 (by decide)))

theorem fz1_120_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨39, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 39 (by decide)))

theorem fz1_120_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨40, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 40 (by decide)))

theorem fz1_120_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨41, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 41 (by decide)))

theorem fz1_120_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨43, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 43 (by decide)))

theorem fz1_120_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨44, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 44 (by decide)))

theorem fz1_120_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨45, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 45 (by decide)))

theorem fz1_120_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨46, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 46 (by decide)))

theorem fz1_120_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨48, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 48 (by decide)))

theorem fz1_120_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨49, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 49 (by decide)))

theorem fz1_120_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨50, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 50 (by decide)))

theorem fz1_120_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨51, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 51 (by decide)))

theorem fz1_120_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨54, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 54 (by decide)))

theorem fz1_120_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨55, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 55 (by decide)))

theorem fz1_120_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨56, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 56 (by decide)))

theorem fz1_120_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨57, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 57 (by decide)))

theorem fz1_120_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨58, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 58 (by decide)))

theorem fz1_120_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨59, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 59 (by decide)))

theorem fz1_120_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨60, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 60 (by decide)))

theorem fz1_120_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨61, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 61 (by decide)))

theorem fz1_120_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨62, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 62 (by decide)))

theorem fz1_120_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨63, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 63 (by decide)))

theorem fz1_120_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨64, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 64 (by decide)))

theorem fz1_120_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨65, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 65 (by decide)))

theorem fz1_120_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨66, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 66 (by decide)))

theorem fz1_120_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨67, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 67 (by decide)))

theorem fz1_120_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨68, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 68 (by decide)))

theorem fz1_120_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨69, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 69 (by decide)))

theorem fz1_120_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨70, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 70 (by decide)))

theorem fz1_120_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨71, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 71 (by decide)))

theorem fz1_120_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨72, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 72 (by decide)))

theorem fz1_120_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨73, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 73 (by decide)))

theorem fz1_120_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨74, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 74 (by decide)))

theorem fz1_120_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨81, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 81 (by decide)))

theorem fz1_120_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨82, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 82 (by decide)))

theorem fz1_120_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨83, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 83 (by decide)))

theorem fz1_120_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨84, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 84 (by decide)))

theorem fz1_120_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨85, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 85 (by decide)))

theorem fz1_120_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨86, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 86 (by decide)))

theorem fz1_120_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨87, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 87 (by decide)))

theorem fz1_120_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨88, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 88 (by decide)))

theorem fz1_120_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨89, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 89 (by decide)))

theorem fz1_120_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨90, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 90 (by decide)))

theorem fz1_120_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨91, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 91 (by decide)))

theorem fz1_120_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨92, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 92 (by decide)))

theorem fz1_120_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨93, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 93 (by decide)))

theorem fz1_120_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨95, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 95 (by decide)))

theorem fz1_120_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨96, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 96 (by decide)))

theorem fz1_120_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨97, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 97 (by decide)))

theorem fz1_120_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨98, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 98 (by decide)))

theorem fz1_120_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨100, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 100 (by decide)))

theorem fz1_120_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨101, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 101 (by decide)))

theorem fz1_120_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨102, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 102 (by decide)))

theorem fz1_120_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨103, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 103 (by decide)))

theorem fz1_120_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨105, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 105 (by decide)))

theorem fz1_120_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨106, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 106 (by decide)))

theorem fz1_120_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨107, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 107 (by decide)))

theorem fz1_120_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨108, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 108 (by decide)))

theorem fz1_120_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨110, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 110 (by decide)))

theorem fz1_120_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨111, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 111 (by decide)))

theorem fz1_120_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨112, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 112 (by decide)))

theorem fz1_120_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨113, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 113 (by decide)))

theorem fz1_120_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨115, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 115 (by decide)))

theorem fz1_120_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨116, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 116 (by decide)))

theorem fz1_120_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨117, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 117 (by decide)))

theorem fz1_120_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨118, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 118 (by decide)))

theorem fz1_120_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨119, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 119 (by decide)))

theorem fz1_120_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨121, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 121 (by decide)))

theorem fz1_120_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨122, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 122 (by decide)))

theorem fz1_120_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨123, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 123 (by decide)))

theorem fz1_120_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨124, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 124 (by decide)))

theorem fz1_120_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨125, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 125 (by decide)))

theorem fz1_120_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨126, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 126 (by decide)))

theorem fz1_120_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨127, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 127 (by decide)))

theorem fz1_120_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨128, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 128 (by decide)))

theorem fz1_120_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨129, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 129 (by decide)))

theorem fz1_120_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨130, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 130 (by decide)))

theorem fz1_120_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨131, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 131 (by decide)))

theorem fz1_120_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨132, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 132 (by decide)))

theorem fz1_120_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨133, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 133 (by decide)))

theorem fz1_120_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨134, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 134 (by decide)))

theorem fz1_120_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨135, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 135 (by decide)))

theorem fz1_120_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨136, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 136 (by decide)))

theorem fz1_120_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨137, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 137 (by decide)))

theorem fz1_120_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨138, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 138 (by decide)))

theorem fz1_120_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨139, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 139 (by decide)))

theorem fz1_120_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨140, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 140 (by decide)))

theorem fz1_120_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨141, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 141 (by decide)))

theorem fz1_120_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨142, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 142 (by decide)))

theorem fz1_120_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨143, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 143 (by decide)))

theorem fz1_120_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨144, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 144 (by decide)))

theorem fz1_120_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨145, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 145 (by decide)))

theorem fz1_120_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK120)) = 0 :=
  repsFixedCard rK120 ⟨146, by decide⟩ R120 hpxR120 hcardq120
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_120) 146 (by decide)))

theorem fixz2_120 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 97, 98, 100, 101, 102, 103, 105, 106, 107, 108, 110, 111, 112, 113, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK120) (retConj 2 (Q2.R120_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_120_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨2, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 2 (by decide)))

theorem fz2_120_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨3, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 3 (by decide)))

theorem fz2_120_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨4, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 4 (by decide)))

theorem fz2_120_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨5, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 5 (by decide)))

theorem fz2_120_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨11, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 11 (by decide)))

theorem fz2_120_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨14, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 14 (by decide)))

theorem fz2_120_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨15, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 15 (by decide)))

theorem fz2_120_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨16, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 16 (by decide)))

theorem fz2_120_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨17, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 17 (by decide)))

theorem fz2_120_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨18, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 18 (by decide)))

theorem fz2_120_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨20, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 20 (by decide)))

theorem fz2_120_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨21, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 21 (by decide)))

theorem fz2_120_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨22, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 22 (by decide)))

theorem fz2_120_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨23, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 23 (by decide)))

theorem fz2_120_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨28, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 28 (by decide)))

theorem fz2_120_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨29, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 29 (by decide)))

theorem fz2_120_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨30, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 30 (by decide)))

theorem fz2_120_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨31, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 31 (by decide)))

theorem fz2_120_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨33, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 33 (by decide)))

theorem fz2_120_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨34, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 34 (by decide)))

theorem fz2_120_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨35, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 35 (by decide)))

theorem fz2_120_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨36, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 36 (by decide)))

theorem fz2_120_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨38, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 38 (by decide)))

theorem fz2_120_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨39, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 39 (by decide)))

theorem fz2_120_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨40, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 40 (by decide)))

theorem fz2_120_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨41, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 41 (by decide)))

theorem fz2_120_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨43, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 43 (by decide)))

theorem fz2_120_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨44, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 44 (by decide)))

theorem fz2_120_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨45, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 45 (by decide)))

theorem fz2_120_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨46, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 46 (by decide)))

theorem fz2_120_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨48, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 48 (by decide)))

theorem fz2_120_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨49, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 49 (by decide)))

theorem fz2_120_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨50, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 50 (by decide)))

theorem fz2_120_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨51, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 51 (by decide)))

theorem fz2_120_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨54, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 54 (by decide)))

theorem fz2_120_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨55, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 55 (by decide)))

theorem fz2_120_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨56, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 56 (by decide)))

theorem fz2_120_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨57, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 57 (by decide)))

theorem fz2_120_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨58, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 58 (by decide)))

theorem fz2_120_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨59, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 59 (by decide)))

theorem fz2_120_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨60, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 60 (by decide)))

theorem fz2_120_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨61, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 61 (by decide)))

theorem fz2_120_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨62, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 62 (by decide)))

theorem fz2_120_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨63, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 63 (by decide)))

theorem fz2_120_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨64, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 64 (by decide)))

theorem fz2_120_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨65, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 65 (by decide)))

theorem fz2_120_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨66, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 66 (by decide)))

theorem fz2_120_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨67, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 67 (by decide)))

theorem fz2_120_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨68, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 68 (by decide)))

theorem fz2_120_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨69, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 69 (by decide)))

theorem fz2_120_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨70, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 70 (by decide)))

theorem fz2_120_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨71, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 71 (by decide)))

theorem fz2_120_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨72, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 72 (by decide)))

theorem fz2_120_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨73, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 73 (by decide)))

theorem fz2_120_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨74, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 74 (by decide)))

theorem fz2_120_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨81, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 81 (by decide)))

theorem fz2_120_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨82, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 82 (by decide)))

theorem fz2_120_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨83, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 83 (by decide)))

theorem fz2_120_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨84, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 84 (by decide)))

theorem fz2_120_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨85, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 85 (by decide)))

theorem fz2_120_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨86, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 86 (by decide)))

theorem fz2_120_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨87, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 87 (by decide)))

theorem fz2_120_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨88, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 88 (by decide)))

theorem fz2_120_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨89, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 89 (by decide)))

theorem fz2_120_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨90, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 90 (by decide)))

theorem fz2_120_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨91, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 91 (by decide)))

theorem fz2_120_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨92, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 92 (by decide)))

theorem fz2_120_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨93, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 93 (by decide)))

theorem fz2_120_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨95, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 95 (by decide)))

theorem fz2_120_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨96, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 96 (by decide)))

theorem fz2_120_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨97, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 97 (by decide)))

theorem fz2_120_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨98, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 98 (by decide)))

theorem fz2_120_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨100, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 100 (by decide)))

theorem fz2_120_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨101, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 101 (by decide)))

theorem fz2_120_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨102, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 102 (by decide)))

theorem fz2_120_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨103, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 103 (by decide)))

theorem fz2_120_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨105, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 105 (by decide)))

theorem fz2_120_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨106, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 106 (by decide)))

theorem fz2_120_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨107, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 107 (by decide)))

theorem fz2_120_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨108, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 108 (by decide)))

theorem fz2_120_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨110, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 110 (by decide)))

theorem fz2_120_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨111, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 111 (by decide)))

theorem fz2_120_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨112, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 112 (by decide)))

theorem fz2_120_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨113, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 113 (by decide)))

theorem fz2_120_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨115, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 115 (by decide)))

theorem fz2_120_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨116, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 116 (by decide)))

theorem fz2_120_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨117, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 117 (by decide)))

theorem fz2_120_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨118, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 118 (by decide)))

theorem fz2_120_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨119, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 119 (by decide)))

theorem fz2_120_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨121, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 121 (by decide)))

theorem fz2_120_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨122, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 122 (by decide)))

theorem fz2_120_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨123, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 123 (by decide)))

theorem fz2_120_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨124, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 124 (by decide)))

theorem fz2_120_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨125, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 125 (by decide)))

theorem fz2_120_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨126, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 126 (by decide)))

theorem fz2_120_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨127, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 127 (by decide)))

theorem fz2_120_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨128, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 128 (by decide)))

theorem fz2_120_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨129, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 129 (by decide)))

theorem fz2_120_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨130, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 130 (by decide)))

theorem fz2_120_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨131, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 131 (by decide)))

theorem fz2_120_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨132, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 132 (by decide)))

theorem fz2_120_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨133, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 133 (by decide)))

theorem fz2_120_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨134, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 134 (by decide)))

theorem fz2_120_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨135, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 135 (by decide)))

theorem fz2_120_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨136, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 136 (by decide)))

theorem fz2_120_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨137, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 137 (by decide)))

theorem fz2_120_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨138, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 138 (by decide)))

theorem fz2_120_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨139, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 139 (by decide)))

theorem fz2_120_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨140, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 140 (by decide)))

theorem fz2_120_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨141, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 141 (by decide)))

theorem fz2_120_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨142, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 142 (by decide)))

theorem fz2_120_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨143, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 143 (by decide)))

theorem fz2_120_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨144, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 144 (by decide)))

theorem fz2_120_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨145, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 145 (by decide)))

theorem fz2_120_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK120)) = 0 :=
  Q2.repsFixedCard2 rK120 ⟨146, by decide⟩ Q2.R120_2 Q2.hpxR120_2 Q2.hcardq120_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_120) 146 (by decide)))

end LeanDring.P5Presentation
