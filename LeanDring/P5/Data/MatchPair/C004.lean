/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C013
import LeanDring.P5.Data.MatchLeaf.C014
import LeanDring.P5.Data.MatchLeaf.C015
import LeanDring.P5.Data.MatchLeaf.C016
import LeanDring.P5.Data.MatchLeaf.C017
import LeanDring.P5.Data.MatchLeaf.C018

/-! # Stage-5 per-pair theorems, chunk 3 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_79_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_52_20 hp j hj hq
  simp at hm

theorem pair_79_79 (p : Nat) (hp : p < (Q2.transData.getD 79 []).length)
    (hrep : (Q2.cosetIsRep.getD 79 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ p hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ p (transLenTr ⟨79, by decide⟩ p hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_79 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_79_24 hp j hj hq
  simp at hm

theorem pair_80_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_1_4 hp j hj hq
  simp at hm

theorem pair_80_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_6_4 hp j hj hq
  simp at hm

theorem pair_80_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_7_4 hp j hj hq
  simp at hm

theorem pair_80_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_8_4 hp j hj hq
  simp at hm

theorem pair_80_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_9_4 hp j hj hq
  simp at hm

theorem pair_80_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_10_4 hp j hj hq
  simp at hm

theorem pair_80_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_12_4 hp j hj hq
  simp at hm

theorem pair_80_13 (p : Nat) (hp : p < (Q2.transData.getD 13 []).length)
    (hrep : (Q2.cosetIsRep.getD 13 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ p (transLenTr ⟨13, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_13 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_13_24 hp j hj hq
  simp at hm

theorem pair_80_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_19_20 hp j hj hq
  simp at hm

theorem pair_80_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_24_20 hp j hj hq
  simp at hm

theorem pair_80_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_25_20 hp j hj hq
  simp at hm

theorem pair_80_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_26_20 hp j hj hq
  simp at hm

theorem pair_80_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_27_20 hp j hj hq
  simp at hm

theorem pair_80_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_53_20 hp j hj hq
  simp at hm

theorem pair_80_80 (p : Nat) (hp : p < (Q2.transData.getD 80 []).length)
    (hrep : (Q2.cosetIsRep.getD 80 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ p hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ p (transLenTr ⟨80, by decide⟩ p hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_80 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_80_80_120 hp j hj hq
  simp at hm

theorem pair_81_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_2_4 hp j hj hq
  simp at hm

theorem pair_81_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_10_4 hp j hj hq
  simp at hm

theorem pair_81_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_12_4 hp j hj hq
  simp at hm

theorem pair_81_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_20_20 hp j hj hq
  simp at hm

theorem pair_81_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_53_20 hp j hj hq
  simp at hm

theorem pair_81_81 (p : Nat) (hp : p < (Q2.transData.getD 81 []).length)
    (hrep : (Q2.cosetIsRep.getD 81 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ p hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ p (transLenTr ⟨81, by decide⟩ p hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_81 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_81_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_81_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_81_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_81_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_81_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_81_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_81_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_81_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_81_81_20 hp j hj hq
  simp at hm

theorem pair_82_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_3_4 hp j hj hq
  simp at hm

theorem pair_82_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_10_4 hp j hj hq
  simp at hm

theorem pair_82_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_12_4 hp j hj hq
  simp at hm

theorem pair_82_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_21_20 hp j hj hq
  simp at hm

theorem pair_82_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_53_20 hp j hj hq
  simp at hm

theorem pair_82_82 (p : Nat) (hp : p < (Q2.transData.getD 82 []).length)
    (hrep : (Q2.cosetIsRep.getD 82 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ p hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ p (transLenTr ⟨82, by decide⟩ p hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_82 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_82_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_82_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_82_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_82_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_82_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_82_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_82_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_82_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_82_82_20 hp j hj hq
  simp at hm

theorem pair_83_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_4_4 hp j hj hq
  simp at hm

theorem pair_83_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_10_4 hp j hj hq
  simp at hm

theorem pair_83_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_12_4 hp j hj hq
  simp at hm

theorem pair_83_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_22_20 hp j hj hq
  simp at hm

theorem pair_83_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_53_20 hp j hj hq
  simp at hm

theorem pair_83_83 (p : Nat) (hp : p < (Q2.transData.getD 83 []).length)
    (hrep : (Q2.cosetIsRep.getD 83 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ p hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ p (transLenTr ⟨83, by decide⟩ p hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_83 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_83_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_83_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_83_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_83_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_83_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_83_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_83_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_83_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_83_83_20 hp j hj hq
  simp at hm

theorem pair_84_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_5_4 hp j hj hq
  simp at hm

theorem pair_84_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_10_4 hp j hj hq
  simp at hm

theorem pair_84_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_12_4 hp j hj hq
  simp at hm

theorem pair_84_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_23_20 hp j hj hq
  simp at hm

theorem pair_84_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_53_20 hp j hj hq
  simp at hm

theorem pair_84_84 (p : Nat) (hp : p < (Q2.transData.getD 84 []).length)
    (hrep : (Q2.cosetIsRep.getD 84 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ p hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ p (transLenTr ⟨84, by decide⟩ p hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_84 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_84_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_84_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_84_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_84_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_84_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_84_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_84_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_84_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_84_84_20 hp j hj hq
  simp at hm

theorem pair_85_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_2_4 hp j hj hq
  simp at hm

theorem pair_85_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_3_4 hp j hj hq
  simp at hm

theorem pair_85_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_4_4 hp j hj hq
  simp at hm

theorem pair_85_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_5_4 hp j hj hq
  simp at hm

theorem pair_85_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_9_4 hp j hj hq
  simp at hm

theorem pair_85_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_11_4 hp j hj hq
  simp at hm

theorem pair_85_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_12_4 hp j hj hq
  simp at hm

theorem pair_85_14 (p : Nat) (hp : p < (Q2.transData.getD 14 []).length)
    (hrep : (Q2.cosetIsRep.getD 14 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ p (transLenTr ⟨14, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_14 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_14_24 hp j hj hq
  simp at hm

theorem pair_85_15 (p : Nat) (hp : p < (Q2.transData.getD 15 []).length)
    (hrep : (Q2.cosetIsRep.getD 15 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ p (transLenTr ⟨15, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_15 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_15_24 hp j hj hq
  simp at hm

theorem pair_85_16 (p : Nat) (hp : p < (Q2.transData.getD 16 []).length)
    (hrep : (Q2.cosetIsRep.getD 16 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ p (transLenTr ⟨16, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_16 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_16_24 hp j hj hq
  simp at hm

theorem pair_85_17 (p : Nat) (hp : p < (Q2.transData.getD 17 []).length)
    (hrep : (Q2.cosetIsRep.getD 17 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ p (transLenTr ⟨17, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_17 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_17_24 hp j hj hq
  simp at hm

theorem pair_85_18 (p : Nat) (hp : p < (Q2.transData.getD 18 []).length)
    (hrep : (Q2.cosetIsRep.getD 18 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ p (transLenTr ⟨18, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_18 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_18_24 hp j hj hq
  simp at hm

theorem pair_85_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_20_20 hp j hj hq
  simp at hm

theorem pair_85_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_21_20 hp j hj hq
  simp at hm

theorem pair_85_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_22_20 hp j hj hq
  simp at hm

theorem pair_85_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_23_20 hp j hj hq
  simp at hm

theorem pair_85_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_27_20 hp j hj hq
  simp at hm

theorem pair_85_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_54_20 hp j hj hq
  simp at hm

theorem pair_85_85 (p : Nat) (hp : p < (Q2.transData.getD 85 []).length)
    (hrep : (Q2.cosetIsRep.getD 85 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ p hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ p (transLenTr ⟨85, by decide⟩ p hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_85 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_85_85_120 hp j hj hq
  simp at hm

theorem pair_86_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_1_4 hp j hj hq
  simp at hm

theorem pair_86_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_2_4 hp j hj hq
  simp at hm

theorem pair_86_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_3_4 hp j hj hq
  simp at hm

theorem pair_86_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_4_4 hp j hj hq
  simp at hm

theorem pair_86_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_5_4 hp j hj hq
  simp at hm

theorem pair_86_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_11_4 hp j hj hq
  simp at hm

theorem pair_86_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_12_4 hp j hj hq
  simp at hm

theorem pair_86_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_19_20 hp j hj hq
  simp at hm

theorem pair_86_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_20_20 hp j hj hq
  simp at hm

theorem pair_86_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_21_20 hp j hj hq
  simp at hm

theorem pair_86_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_22_20 hp j hj hq
  simp at hm

theorem pair_86_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_23_20 hp j hj hq
  simp at hm

theorem pair_86_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_54_20 hp j hj hq
  simp at hm

theorem pair_86_86 (p : Nat) (hp : p < (Q2.transData.getD 86 []).length)
    (hrep : (Q2.cosetIsRep.getD 86 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ p hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ p (transLenTr ⟨86, by decide⟩ p hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_86 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_86_86_24 hp j hj hq
  simp at hm

theorem pair_87_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_2_4 hp j hj hq
  simp at hm

theorem pair_87_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_3_4 hp j hj hq
  simp at hm

theorem pair_87_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_4_4 hp j hj hq
  simp at hm

theorem pair_87_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_5_4 hp j hj hq
  simp at hm

theorem pair_87_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_7_4 hp j hj hq
  simp at hm

theorem pair_87_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_11_4 hp j hj hq
  simp at hm

theorem pair_87_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_12_4 hp j hj hq
  simp at hm

theorem pair_87_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_20_20 hp j hj hq
  simp at hm

theorem pair_87_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_21_20 hp j hj hq
  simp at hm

theorem pair_87_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_22_20 hp j hj hq
  simp at hm

theorem pair_87_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_23_20 hp j hj hq
  simp at hm

theorem pair_87_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_25_20 hp j hj hq
  simp at hm

theorem pair_87_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_54_20 hp j hj hq
  simp at hm

theorem pair_87_87 (p : Nat) (hp : p < (Q2.transData.getD 87 []).length)
    (hrep : (Q2.cosetIsRep.getD 87 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ p hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ p (transLenTr ⟨87, by decide⟩ p hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_87 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_87_87_24 hp j hj hq
  simp at hm

theorem pair_88_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_2_4 hp j hj hq
  simp at hm

theorem pair_88_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_3_4 hp j hj hq
  simp at hm

theorem pair_88_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_4_4 hp j hj hq
  simp at hm

theorem pair_88_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_5_4 hp j hj hq
  simp at hm

theorem pair_88_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_6_4 hp j hj hq
  simp at hm

theorem pair_88_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_11_4 hp j hj hq
  simp at hm

theorem pair_88_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_12_4 hp j hj hq
  simp at hm

theorem pair_88_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_20_20 hp j hj hq
  simp at hm

theorem pair_88_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_21_20 hp j hj hq
  simp at hm

theorem pair_88_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_22_20 hp j hj hq
  simp at hm

theorem pair_88_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_23_20 hp j hj hq
  simp at hm

theorem pair_88_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_24_20 hp j hj hq
  simp at hm

theorem pair_88_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_54_20 hp j hj hq
  simp at hm

theorem pair_88_88 (p : Nat) (hp : p < (Q2.transData.getD 88 []).length)
    (hrep : (Q2.cosetIsRep.getD 88 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ p hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ p (transLenTr ⟨88, by decide⟩ p hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_88 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_88_88_24 hp j hj hq
  simp at hm

theorem pair_89_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_2_4 hp j hj hq
  simp at hm

theorem pair_89_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_3_4 hp j hj hq
  simp at hm

theorem pair_89_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_4_4 hp j hj hq
  simp at hm

theorem pair_89_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_5_4 hp j hj hq
  simp at hm

theorem pair_89_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_8_4 hp j hj hq
  simp at hm

theorem pair_89_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_11_4 hp j hj hq
  simp at hm

theorem pair_89_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_12_4 hp j hj hq
  simp at hm

theorem pair_89_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_20_20 hp j hj hq
  simp at hm

theorem pair_89_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_21_20 hp j hj hq
  simp at hm

theorem pair_89_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_22_20 hp j hj hq
  simp at hm

theorem pair_89_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_23_20 hp j hj hq
  simp at hm

theorem pair_89_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_26_20 hp j hj hq
  simp at hm

theorem pair_89_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_54_20 hp j hj hq
  simp at hm

theorem pair_89_89 (p : Nat) (hp : p < (Q2.transData.getD 89 []).length)
    (hrep : (Q2.cosetIsRep.getD 89 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ p hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ p (transLenTr ⟨89, by decide⟩ p hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_89 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_89_89_24 hp j hj hq
  simp at hm

theorem pair_90_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_10_4 hp j hj hq
  simp at hm

theorem pair_90_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_12_4 hp j hj hq
  simp at hm

theorem pair_90_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_28_20 hp j hj hq
  simp at hm

theorem pair_90_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_53_20 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
