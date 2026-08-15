/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C033
import LeanDring.P5.Data.MatchLeaf.C034
import LeanDring.P5.Data.MatchLeaf.C035
import LeanDring.P5.Data.MatchLeaf.C036
import LeanDring.P5.Data.MatchLeaf.C037

/-! # Stage-5 per-pair theorems, chunk 7 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_125_81 (p : Nat) (hp : p < (Q2.transData.getD 81 []).length)
    (hrep : (Q2.cosetIsRep.getD 81 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ p (transLenTr ⟨81, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_81 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_81_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_81_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_81_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_81_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_81_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_81_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_81_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_81_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_81_20 hp j hj hq
  simp at hm

theorem pair_125_93 (p : Nat) (hp : p < (Q2.transData.getD 93 []).length)
    (hrep : (Q2.cosetIsRep.getD 93 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ p (transLenTr ⟨93, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_93 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_93_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_93_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_93_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_93_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_93_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_93_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_93_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_93_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_93_20 hp j hj hq
  simp at hm

theorem pair_125_96 (p : Nat) (hp : p < (Q2.transData.getD 96 []).length)
    (hrep : (Q2.cosetIsRep.getD 96 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ p (transLenTr ⟨96, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_96 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_96_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_96_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_96_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_96_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_96_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_96_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_96_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_96_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_96_20 hp j hj hq
  simp at hm

theorem pair_125_102 (p : Nat) (hp : p < (Q2.transData.getD 102 []).length)
    (hrep : (Q2.cosetIsRep.getD 102 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ p (transLenTr ⟨102, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_102 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_102_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_102_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_102_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_102_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_102_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_102_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_102_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_102_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_102_20 hp j hj hq
  simp at hm

theorem pair_125_105 (p : Nat) (hp : p < (Q2.transData.getD 105 []).length)
    (hrep : (Q2.cosetIsRep.getD 105 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ p (transLenTr ⟨105, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_105 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_105_100 hp j hj hq
  simp at hm

theorem pair_125_114 (p : Nat) (hp : p < (Q2.transData.getD 114 []).length)
    (hrep : (Q2.cosetIsRep.getD 114 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ p (transLenTr ⟨114, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_114 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_114_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_114_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_114_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_114_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_114_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_114_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_114_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_114_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_114_20 hp j hj hq
  simp at hm

theorem pair_125_125 (p : Nat) (hp : p < (Q2.transData.getD 125 []).length)
    (hrep : (Q2.cosetIsRep.getD 125 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ p (transLenTr ⟨125, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_125 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_125_24 hp j hj hq
  simp at hm

theorem pair_126_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_3_4 hp j hj hq
  simp at hm

theorem pair_126_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_10_4 hp j hj hq
  simp at hm

theorem pair_126_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_12_4 hp j hj hq
  simp at hm

theorem pair_126_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_21_20 hp j hj hq
  simp at hm

theorem pair_126_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_31_20 hp j hj hq
  simp at hm

theorem pair_126_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_37_20 hp j hj hq
  simp at hm

theorem pair_126_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_39_20 hp j hj hq
  simp at hm

theorem pair_126_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_45_20 hp j hj hq
  simp at hm

theorem pair_126_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_48_20 hp j hj hq
  simp at hm

theorem pair_126_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_53_20 hp j hj hq
  simp at hm

theorem pair_126_82 (p : Nat) (hp : p < (Q2.transData.getD 82 []).length)
    (hrep : (Q2.cosetIsRep.getD 82 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ p (transLenTr ⟨82, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_82 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_82_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_82_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_82_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_82_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_82_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_82_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_82_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_82_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_82_20 hp j hj hq
  simp at hm

theorem pair_126_93 (p : Nat) (hp : p < (Q2.transData.getD 93 []).length)
    (hrep : (Q2.cosetIsRep.getD 93 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ p (transLenTr ⟨93, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_93 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_93_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_93_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_93_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_93_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_93_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_93_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_93_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_93_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_93_20 hp j hj hq
  simp at hm

theorem pair_126_99 (p : Nat) (hp : p < (Q2.transData.getD 99 []).length)
    (hrep : (Q2.cosetIsRep.getD 99 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ p (transLenTr ⟨99, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_99 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_99_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_99_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_99_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_99_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_99_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_99_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_99_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_99_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_99_20 hp j hj hq
  simp at hm

theorem pair_126_101 (p : Nat) (hp : p < (Q2.transData.getD 101 []).length)
    (hrep : (Q2.cosetIsRep.getD 101 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ p (transLenTr ⟨101, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_101 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_101_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_101_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_101_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_101_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_101_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_101_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_101_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_101_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_101_20 hp j hj hq
  simp at hm

theorem pair_126_107 (p : Nat) (hp : p < (Q2.transData.getD 107 []).length)
    (hrep : (Q2.cosetIsRep.getD 107 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ p (transLenTr ⟨107, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_107 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_107_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_107_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_107_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_107_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_107_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_107_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_107_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_107_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_107_20 hp j hj hq
  simp at hm

theorem pair_126_110 (p : Nat) (hp : p < (Q2.transData.getD 110 []).length)
    (hrep : (Q2.cosetIsRep.getD 110 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ p (transLenTr ⟨110, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_110 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_110_100 hp j hj hq
  simp at hm

theorem pair_126_126 (p : Nat) (hp : p < (Q2.transData.getD 126 []).length)
    (hrep : (Q2.cosetIsRep.getD 126 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ p hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ p (transLenTr ⟨126, by decide⟩ p hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_126 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_126_126_24 hp j hj hq
  simp at hm

theorem pair_127_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_3_4 hp j hj hq
  simp at hm

theorem pair_127_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_10_4 hp j hj hq
  simp at hm

theorem pair_127_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_12_4 hp j hj hq
  simp at hm

theorem pair_127_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_21_20 hp j hj hq
  simp at hm

theorem pair_127_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_32_20 hp j hj hq
  simp at hm

theorem pair_127_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_33_20 hp j hj hq
  simp at hm

theorem pair_127_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_40_20 hp j hj hq
  simp at hm

theorem pair_127_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_46_20 hp j hj hq
  simp at hm

theorem pair_127_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_49_20 hp j hj hq
  simp at hm

theorem pair_127_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_53_20 hp j hj hq
  simp at hm

theorem pair_127_82 (p : Nat) (hp : p < (Q2.transData.getD 82 []).length)
    (hrep : (Q2.cosetIsRep.getD 82 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ p (transLenTr ⟨82, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_82 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_82_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_82_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_82_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_82_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_82_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_82_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_82_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_82_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_82_20 hp j hj hq
  simp at hm

theorem pair_127_94 (p : Nat) (hp : p < (Q2.transData.getD 94 []).length)
    (hrep : (Q2.cosetIsRep.getD 94 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ p (transLenTr ⟨94, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_94 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_94_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_94_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_94_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_94_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_94_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_94_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_94_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_94_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_94_20 hp j hj hq
  simp at hm

theorem pair_127_95 (p : Nat) (hp : p < (Q2.transData.getD 95 []).length)
    (hrep : (Q2.cosetIsRep.getD 95 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ p (transLenTr ⟨95, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_95 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_95_100 hp j hj hq
  simp at hm

theorem pair_127_102 (p : Nat) (hp : p < (Q2.transData.getD 102 []).length)
    (hrep : (Q2.cosetIsRep.getD 102 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ p (transLenTr ⟨102, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_102 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_102_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_102_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_102_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_102_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_102_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_102_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_102_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_102_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_102_20 hp j hj hq
  simp at hm

theorem pair_127_108 (p : Nat) (hp : p < (Q2.transData.getD 108 []).length)
    (hrep : (Q2.cosetIsRep.getD 108 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ p (transLenTr ⟨108, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_108 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_108_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_108_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_108_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_108_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_108_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_108_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_108_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_108_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_108_20 hp j hj hq
  simp at hm

theorem pair_127_111 (p : Nat) (hp : p < (Q2.transData.getD 111 []).length)
    (hrep : (Q2.cosetIsRep.getD 111 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ p (transLenTr ⟨111, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_111 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_111_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_111_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_111_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_111_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_111_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_111_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_111_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_111_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_111_20 hp j hj hq
  simp at hm

theorem pair_127_127 (p : Nat) (hp : p < (Q2.transData.getD 127 []).length)
    (hrep : (Q2.cosetIsRep.getD 127 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ p hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ p (transLenTr ⟨127, by decide⟩ p hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_127 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_127_127_24 hp j hj hq
  simp at hm

theorem pair_128_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_3_4 hp j hj hq
  simp at hm

theorem pair_128_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_10_4 hp j hj hq
  simp at hm

theorem pair_128_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_12_4 hp j hj hq
  simp at hm

theorem pair_128_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_21_20 hp j hj hq
  simp at hm

theorem pair_128_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_28_20 hp j hj hq
  simp at hm

theorem pair_128_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_34_20 hp j hj hq
  simp at hm

theorem pair_128_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_41_20 hp j hj hq
  simp at hm

theorem pair_128_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_47_20 hp j hj hq
  simp at hm

theorem pair_128_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_50_20 hp j hj hq
  simp at hm

theorem pair_128_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_53_20 hp j hj hq
  simp at hm

theorem pair_128_82 (p : Nat) (hp : p < (Q2.transData.getD 82 []).length)
    (hrep : (Q2.cosetIsRep.getD 82 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ p (transLenTr ⟨82, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_82 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_82_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_82_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_82_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_82_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_82_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_82_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_82_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_82_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_82_20 hp j hj hq
  simp at hm

theorem pair_128_90 (p : Nat) (hp : p < (Q2.transData.getD 90 []).length)
    (hrep : (Q2.cosetIsRep.getD 90 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ p (transLenTr ⟨90, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_90 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_90_100 hp j hj hq
  simp at hm

theorem pair_128_96 (p : Nat) (hp : p < (Q2.transData.getD 96 []).length)
    (hrep : (Q2.cosetIsRep.getD 96 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ p (transLenTr ⟨96, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_96 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_96_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_96_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_96_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_96_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_96_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_96_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_96_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_96_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_96_20 hp j hj hq
  simp at hm

theorem pair_128_103 (p : Nat) (hp : p < (Q2.transData.getD 103 []).length)
    (hrep : (Q2.cosetIsRep.getD 103 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ p (transLenTr ⟨103, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_103 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_103_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_103_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_103_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_103_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_103_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_103_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_103_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_103_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_103_20 hp j hj hq
  simp at hm

theorem pair_128_109 (p : Nat) (hp : p < (Q2.transData.getD 109 []).length)
    (hrep : (Q2.cosetIsRep.getD 109 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ p (transLenTr ⟨109, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_109 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_109_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_109_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_109_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_109_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_109_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_109_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_109_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_109_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_109_20 hp j hj hq
  simp at hm

theorem pair_128_112 (p : Nat) (hp : p < (Q2.transData.getD 112 []).length)
    (hrep : (Q2.cosetIsRep.getD 112 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ p (transLenTr ⟨112, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_112 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_112_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_112_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_112_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_112_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_112_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_112_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_112_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_112_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_112_20 hp j hj hq
  simp at hm

theorem pair_128_128 (p : Nat) (hp : p < (Q2.transData.getD 128 []).length)
    (hrep : (Q2.cosetIsRep.getD 128 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ p hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ p (transLenTr ⟨128, by decide⟩ p hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_128 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_128_128_24 hp j hj hq
  simp at hm

theorem pair_129_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_3_4 hp j hj hq
  simp at hm

theorem pair_129_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_10_4 hp j hj hq
  simp at hm

theorem pair_129_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_12_4 hp j hj hq
  simp at hm

theorem pair_129_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_21_20 hp j hj hq
  simp at hm

theorem pair_129_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_29_20 hp j hj hq
  simp at hm

theorem pair_129_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_35_20 hp j hj hq
  simp at hm

theorem pair_129_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_42_20 hp j hj hq
  simp at hm

theorem pair_129_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_43_20 hp j hj hq
  simp at hm

theorem pair_129_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_51_20 hp j hj hq
  simp at hm

theorem pair_129_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_53_20 hp j hj hq
  simp at hm

theorem pair_129_82 (p : Nat) (hp : p < (Q2.transData.getD 82 []).length)
    (hrep : (Q2.cosetIsRep.getD 82 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ p (transLenTr ⟨82, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_82 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_82_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_82_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_82_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_82_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_82_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_82_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_82_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_82_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_82_20 hp j hj hq
  simp at hm

theorem pair_129_91 (p : Nat) (hp : p < (Q2.transData.getD 91 []).length)
    (hrep : (Q2.cosetIsRep.getD 91 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ p (transLenTr ⟨91, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_91 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_91_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_91_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_91_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_91_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_91_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_91_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_91_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_91_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_91_20 hp j hj hq
  simp at hm

theorem pair_129_97 (p : Nat) (hp : p < (Q2.transData.getD 97 []).length)
    (hrep : (Q2.cosetIsRep.getD 97 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ p (transLenTr ⟨97, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_97 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_97_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_97_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_97_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_97_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_97_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_97_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_97_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_97_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_97_20 hp j hj hq
  simp at hm

theorem pair_129_104 (p : Nat) (hp : p < (Q2.transData.getD 104 []).length)
    (hrep : (Q2.cosetIsRep.getD 104 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ p (transLenTr ⟨104, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_104 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_104_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_104_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_104_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_104_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_104_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_104_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_104_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_104_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_104_20 hp j hj hq
  simp at hm

theorem pair_129_105 (p : Nat) (hp : p < (Q2.transData.getD 105 []).length)
    (hrep : (Q2.cosetIsRep.getD 105 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ p (transLenTr ⟨105, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_105 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_105_100 hp j hj hq
  simp at hm

theorem pair_129_113 (p : Nat) (hp : p < (Q2.transData.getD 113 []).length)
    (hrep : (Q2.cosetIsRep.getD 113 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ p (transLenTr ⟨113, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_113 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_113_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_113_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_113_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_113_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_113_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_113_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_113_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_113_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_113_20 hp j hj hq
  simp at hm

theorem pair_129_129 (p : Nat) (hp : p < (Q2.transData.getD 129 []).length)
    (hrep : (Q2.cosetIsRep.getD 129 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ p hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ p (transLenTr ⟨129, by decide⟩ p hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_129 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_129_129_24 hp j hj hq
  simp at hm

theorem pair_130_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_3_4 hp j hj hq
  simp at hm

theorem pair_130_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_10_4 hp j hj hq
  simp at hm

theorem pair_130_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_12_4 hp j hj hq
  simp at hm

theorem pair_130_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_21_20 hp j hj hq
  simp at hm

theorem pair_130_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_30_20 hp j hj hq
  simp at hm

theorem pair_130_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_36_20 hp j hj hq
  simp at hm

theorem pair_130_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_38_20 hp j hj hq
  simp at hm

theorem pair_130_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_44_20 hp j hj hq
  simp at hm

theorem pair_130_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_52_20 hp j hj hq
  simp at hm

theorem pair_130_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_53_20 hp j hj hq
  simp at hm

theorem pair_130_82 (p : Nat) (hp : p < (Q2.transData.getD 82 []).length)
    (hrep : (Q2.cosetIsRep.getD 82 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ p (transLenTr ⟨82, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_82 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_82_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_82_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_82_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_82_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_82_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_82_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_82_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_82_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_82_20 hp j hj hq
  simp at hm

theorem pair_130_92 (p : Nat) (hp : p < (Q2.transData.getD 92 []).length)
    (hrep : (Q2.cosetIsRep.getD 92 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ p (transLenTr ⟨92, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_92 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_92_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_92_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_92_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_92_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_92_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_92_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_92_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_92_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_92_20 hp j hj hq
  simp at hm

theorem pair_130_98 (p : Nat) (hp : p < (Q2.transData.getD 98 []).length)
    (hrep : (Q2.cosetIsRep.getD 98 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ p (transLenTr ⟨98, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_98 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_98_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_98_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_98_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_98_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_98_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_98_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_98_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_98_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_98_20 hp j hj hq
  simp at hm

theorem pair_130_100 (p : Nat) (hp : p < (Q2.transData.getD 100 []).length)
    (hrep : (Q2.cosetIsRep.getD 100 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ p (transLenTr ⟨100, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_100 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_100_100 hp j hj hq
  simp at hm

theorem pair_130_106 (p : Nat) (hp : p < (Q2.transData.getD 106 []).length)
    (hrep : (Q2.cosetIsRep.getD 106 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ p (transLenTr ⟨106, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_106 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_106_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_106_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_106_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_106_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_106_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_106_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_106_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_106_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_106_20 hp j hj hq
  simp at hm

theorem pair_130_114 (p : Nat) (hp : p < (Q2.transData.getD 114 []).length)
    (hrep : (Q2.cosetIsRep.getD 114 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ p (transLenTr ⟨114, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_114 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_114_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_114_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_114_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_114_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_114_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_114_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_114_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_114_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_114_20 hp j hj hq
  simp at hm

theorem pair_130_130 (p : Nat) (hp : p < (Q2.transData.getD 130 []).length)
    (hrep : (Q2.cosetIsRep.getD 130 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ p hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ p (transLenTr ⟨130, by decide⟩ p hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_130 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_130_130_24 hp j hj hq
  simp at hm

theorem pair_131_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_4_4 hp j hj hq
  simp at hm

theorem pair_131_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_10_4 hp j hj hq
  simp at hm

theorem pair_131_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_12_4 hp j hj hq
  simp at hm

theorem pair_131_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_22_20 hp j hj hq
  simp at hm

theorem pair_131_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_30_20 hp j hj hq
  simp at hm

theorem pair_131_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_34_20 hp j hj hq
  simp at hm

theorem pair_131_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_42_20 hp j hj hq
  simp at hm

theorem pair_131_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_46_20 hp j hj hq
  simp at hm

theorem pair_131_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_48_20 hp j hj hq
  simp at hm

theorem pair_131_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_53_20 hp j hj hq
  simp at hm

theorem pair_131_83 (p : Nat) (hp : p < (Q2.transData.getD 83 []).length)
    (hrep : (Q2.cosetIsRep.getD 83 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ p (transLenTr ⟨83, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_83 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_83_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_83_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_83_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_83_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_83_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_83_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_83_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_83_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_83_20 hp j hj hq
  simp at hm

theorem pair_131_92 (p : Nat) (hp : p < (Q2.transData.getD 92 []).length)
    (hrep : (Q2.cosetIsRep.getD 92 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ p (transLenTr ⟨92, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_92 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_92_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_92_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_92_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_92_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_92_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_92_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_92_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_92_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_92_20 hp j hj hq
  simp at hm

theorem pair_131_96 (p : Nat) (hp : p < (Q2.transData.getD 96 []).length)
    (hrep : (Q2.cosetIsRep.getD 96 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ p (transLenTr ⟨96, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_96 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_96_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_96_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_96_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_96_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_96_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_96_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_96_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_96_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_96_20 hp j hj hq
  simp at hm

theorem pair_131_104 (p : Nat) (hp : p < (Q2.transData.getD 104 []).length)
    (hrep : (Q2.cosetIsRep.getD 104 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ p (transLenTr ⟨104, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_104 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_104_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_104_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_104_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_104_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_104_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_104_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_104_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_104_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_104_20 hp j hj hq
  simp at hm

theorem pair_131_108 (p : Nat) (hp : p < (Q2.transData.getD 108 []).length)
    (hrep : (Q2.cosetIsRep.getD 108 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ p (transLenTr ⟨108, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_108 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_108_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_108_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_108_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_108_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_108_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_108_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_108_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_108_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_108_20 hp j hj hq
  simp at hm

theorem pair_131_110 (p : Nat) (hp : p < (Q2.transData.getD 110 []).length)
    (hrep : (Q2.cosetIsRep.getD 110 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ p (transLenTr ⟨110, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_110 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_110_100 hp j hj hq
  simp at hm

theorem pair_131_131 (p : Nat) (hp : p < (Q2.transData.getD 131 []).length)
    (hrep : (Q2.cosetIsRep.getD 131 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ p hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ p (transLenTr ⟨131, by decide⟩ p hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_131 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_131_131_24 hp j hj hq
  simp at hm

theorem pair_132_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_4_4 hp j hj hq
  simp at hm

theorem pair_132_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_10_4 hp j hj hq
  simp at hm

theorem pair_132_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_12_4 hp j hj hq
  simp at hm

theorem pair_132_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_22_20 hp j hj hq
  simp at hm

theorem pair_132_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_31_20 hp j hj hq
  simp at hm

theorem pair_132_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_35_20 hp j hj hq
  simp at hm

theorem pair_132_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_38_20 hp j hj hq
  simp at hm

theorem pair_132_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_47_20 hp j hj hq
  simp at hm

theorem pair_132_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_49_20 hp j hj hq
  simp at hm

theorem pair_132_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_53_20 hp j hj hq
  simp at hm

theorem pair_132_83 (p : Nat) (hp : p < (Q2.transData.getD 83 []).length)
    (hrep : (Q2.cosetIsRep.getD 83 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ p hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ p (transLenTr ⟨83, by decide⟩ p hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_83 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_83_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_83_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_83_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_83_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_83_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_83_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_83_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_83_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_132_83_20 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
