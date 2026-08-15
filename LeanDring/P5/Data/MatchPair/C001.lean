/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C001
import LeanDring.P5.Data.MatchLeaf.C002
import LeanDring.P5.Data.MatchLeaf.C003
import LeanDring.P5.Data.MatchLeaf.C004

/-! # Stage-5 per-pair theorems, chunk 0 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_1_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 1 []).length)
    (hq : (normIsRep.getD 1 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨1, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨1, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_1_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_1_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_1_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_1_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_1_1_4 hp j hj hq
  simp at hm

theorem pair_2_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 2 []).length)
    (hq : (normIsRep.getD 2 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨2, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨2, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_2_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_2_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_2_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_2_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_2_2_4 hp j hj hq
  simp at hm

theorem pair_3_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 3 []).length)
    (hq : (normIsRep.getD 3 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨3, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨3, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_3_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_3_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_3_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_3_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_3_3_4 hp j hj hq
  simp at hm

theorem pair_4_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 4 []).length)
    (hq : (normIsRep.getD 4 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨4, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨4, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_4_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_4_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_4_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_4_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_4_4_4 hp j hj hq
  simp at hm

theorem pair_5_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 5 []).length)
    (hq : (normIsRep.getD 5 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨5, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨5, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_5_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_5_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_5_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_5_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_5_5_4 hp j hj hq
  simp at hm

theorem pair_6_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 6 []).length)
    (hq : (normIsRep.getD 6 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨6, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨6, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_6_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_6_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_6_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_6_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_6_6_4 hp j hj hq
  simp at hm

theorem pair_7_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 7 []).length)
    (hq : (normIsRep.getD 7 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨7, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨7, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_7_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_7_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_7_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_7_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_7_7_4 hp j hj hq
  simp at hm

theorem pair_8_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 8 []).length)
    (hq : (normIsRep.getD 8 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨8, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨8, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_8_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_8_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_8_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_8_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_8_8_4 hp j hj hq
  simp at hm

theorem pair_9_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 9 []).length)
    (hq : (normIsRep.getD 9 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨9, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨9, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_9_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_9_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_9_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_9_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_9_9_4 hp j hj hq
  simp at hm

theorem pair_10_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 10 []).length)
    (hq : (normIsRep.getD 10 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨10, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨10, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_10_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_10_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_10_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_10_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_10_10_4 hp j hj hq
  simp at hm

theorem pair_11_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 11 []).length)
    (hq : (normIsRep.getD 11 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨11, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨11, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_11_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_11_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_11_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_11_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_11_11_4 hp j hj hq
  simp at hm

theorem pair_12_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 12 []).length)
    (hq : (normIsRep.getD 12 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨12, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨12, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_12_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_12_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_12_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_12_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_12_12_4 hp j hj hq
  simp at hm

theorem pair_13_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_1_4 hp j hj hq
  simp at hm

theorem pair_13_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_6_4 hp j hj hq
  simp at hm

theorem pair_13_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_7_4 hp j hj hq
  simp at hm

theorem pair_13_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_8_4 hp j hj hq
  simp at hm

theorem pair_13_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_9_4 hp j hj hq
  simp at hm

theorem pair_13_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_10_4 hp j hj hq
  simp at hm

theorem pair_13_13 (p : Nat) (hp : p < (Q2.transData.getD 13 []).length)
    (hrep : (Q2.cosetIsRep.getD 13 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ p hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ p (transLenTr ⟨13, by decide⟩ p hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_13 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_13_13_24 hp j hj hq
  simp at hm

theorem pair_14_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_2_4 hp j hj hq
  simp at hm

theorem pair_14_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_3_4 hp j hj hq
  simp at hm

theorem pair_14_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_4_4 hp j hj hq
  simp at hm

theorem pair_14_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_5_4 hp j hj hq
  simp at hm

theorem pair_14_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_9_4 hp j hj hq
  simp at hm

theorem pair_14_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_11_4 hp j hj hq
  simp at hm

theorem pair_14_14 (p : Nat) (hp : p < (Q2.transData.getD 14 []).length)
    (hrep : (Q2.cosetIsRep.getD 14 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ p hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ p (transLenTr ⟨14, by decide⟩ p hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_14 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_14_14_24 hp j hj hq
  simp at hm

theorem pair_15_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_2_4 hp j hj hq
  simp at hm

theorem pair_15_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_3_4 hp j hj hq
  simp at hm

theorem pair_15_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_4_4 hp j hj hq
  simp at hm

theorem pair_15_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_5_4 hp j hj hq
  simp at hm

theorem pair_15_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_9_4 hp j hj hq
  simp at hm

theorem pair_15_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_11_4 hp j hj hq
  simp at hm

theorem pair_15_15 (p : Nat) (hp : p < (Q2.transData.getD 15 []).length)
    (hrep : (Q2.cosetIsRep.getD 15 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ p hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ p (transLenTr ⟨15, by decide⟩ p hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_15 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_15_15_24 hp j hj hq
  simp at hm

theorem pair_16_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_2_4 hp j hj hq
  simp at hm

theorem pair_16_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_3_4 hp j hj hq
  simp at hm

theorem pair_16_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_4_4 hp j hj hq
  simp at hm

theorem pair_16_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_5_4 hp j hj hq
  simp at hm

theorem pair_16_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_9_4 hp j hj hq
  simp at hm

theorem pair_16_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_11_4 hp j hj hq
  simp at hm

theorem pair_16_16 (p : Nat) (hp : p < (Q2.transData.getD 16 []).length)
    (hrep : (Q2.cosetIsRep.getD 16 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ p hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ p (transLenTr ⟨16, by decide⟩ p hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_16 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_16_16_24 hp j hj hq
  simp at hm

theorem pair_17_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_2_4 hp j hj hq
  simp at hm

theorem pair_17_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_3_4 hp j hj hq
  simp at hm

theorem pair_17_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_4_4 hp j hj hq
  simp at hm

theorem pair_17_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_5_4 hp j hj hq
  simp at hm

theorem pair_17_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_9_4 hp j hj hq
  simp at hm

theorem pair_17_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_11_4 hp j hj hq
  simp at hm

theorem pair_17_17 (p : Nat) (hp : p < (Q2.transData.getD 17 []).length)
    (hrep : (Q2.cosetIsRep.getD 17 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ p hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ p (transLenTr ⟨17, by decide⟩ p hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_17 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_17_17_24 hp j hj hq
  simp at hm

theorem pair_18_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_2_4 hp j hj hq
  simp at hm

theorem pair_18_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_3_4 hp j hj hq
  simp at hm

theorem pair_18_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_4_4 hp j hj hq
  simp at hm

theorem pair_18_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_5_4 hp j hj hq
  simp at hm

theorem pair_18_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_9_4 hp j hj hq
  simp at hm

theorem pair_18_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_11_4 hp j hj hq
  simp at hm

theorem pair_18_18 (p : Nat) (hp : p < (Q2.transData.getD 18 []).length)
    (hrep : (Q2.cosetIsRep.getD 18 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ p hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ p (transLenTr ⟨18, by decide⟩ p hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_18 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_18_18_24 hp j hj hq
  simp at hm

theorem pair_19_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_1_4 hp j hj hq
  simp at hm

theorem pair_19_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_12_4 hp j hj hq
  simp at hm

theorem pair_19_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_19_19_20 hp j hj hq
  simp at hm

theorem pair_20_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_2_4 hp j hj hq
  simp at hm

theorem pair_20_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_12_4 hp j hj hq
  simp at hm

theorem pair_20_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_20_20_20 hp j hj hq
  simp at hm

theorem pair_21_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_3_4 hp j hj hq
  simp at hm

theorem pair_21_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_12_4 hp j hj hq
  simp at hm

theorem pair_21_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_21_21_20 hp j hj hq
  simp at hm

theorem pair_22_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_4_4 hp j hj hq
  simp at hm

theorem pair_22_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_12_4 hp j hj hq
  simp at hm

theorem pair_22_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_22_22_20 hp j hj hq
  simp at hm

theorem pair_23_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_5_4 hp j hj hq
  simp at hm

theorem pair_23_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_12_4 hp j hj hq
  simp at hm

theorem pair_23_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_23_23_20 hp j hj hq
  simp at hm

theorem pair_24_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_6_4 hp j hj hq
  simp at hm

theorem pair_24_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_12_4 hp j hj hq
  simp at hm

theorem pair_24_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_24_24_20 hp j hj hq
  simp at hm

theorem pair_25_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_7_4 hp j hj hq
  simp at hm

theorem pair_25_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_12_4 hp j hj hq
  simp at hm

theorem pair_25_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 25 []).length)
    (hq : (normIsRep.getD 25 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨25, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨25, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_25_25_20 hp j hj hq
  simp at hm

theorem pair_26_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_8_4 hp j hj hq
  simp at hm

theorem pair_26_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_12_4 hp j hj hq
  simp at hm

theorem pair_26_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 26 []).length)
    (hq : (normIsRep.getD 26 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨26, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨26, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_26_26_20 hp j hj hq
  simp at hm

theorem pair_27_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_9_4 hp j hj hq
  simp at hm

theorem pair_27_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_12_4 hp j hj hq
  simp at hm

theorem pair_27_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 27 []).length)
    (hq : (normIsRep.getD 27 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨27, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨27, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_27_27_20 hp j hj hq
  simp at hm

theorem pair_28_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_12_4 hp j hj hq
  simp at hm

theorem pair_28_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 28 []).length)
    (hq : (normIsRep.getD 28 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨28, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨28, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_28_28_20 hp j hj hq
  simp at hm

theorem pair_29_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_12_4 hp j hj hq
  simp at hm

theorem pair_29_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 29 []).length)
    (hq : (normIsRep.getD 29 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨29, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨29, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_29_29_20 hp j hj hq
  simp at hm

theorem pair_30_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_12_4 hp j hj hq
  simp at hm

theorem pair_30_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 30 []).length)
    (hq : (normIsRep.getD 30 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨30, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨30, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_30_30_20 hp j hj hq
  simp at hm

theorem pair_31_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_12_4 hp j hj hq
  simp at hm

theorem pair_31_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 31 []).length)
    (hq : (normIsRep.getD 31 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨31, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨31, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_31_31_20 hp j hj hq
  simp at hm

theorem pair_32_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_12_4 hp j hj hq
  simp at hm

theorem pair_32_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 32 []).length)
    (hq : (normIsRep.getD 32 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨32, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨32, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_32_32_20 hp j hj hq
  simp at hm

theorem pair_33_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_12_4 hp j hj hq
  simp at hm

theorem pair_33_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 33 []).length)
    (hq : (normIsRep.getD 33 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨33, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨33, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_33_33_20 hp j hj hq
  simp at hm

theorem pair_34_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_12_4 hp j hj hq
  simp at hm

theorem pair_34_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 34 []).length)
    (hq : (normIsRep.getD 34 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨34, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨34, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_34_34_20 hp j hj hq
  simp at hm

theorem pair_35_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_12_4 hp j hj hq
  simp at hm

theorem pair_35_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 35 []).length)
    (hq : (normIsRep.getD 35 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨35, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨35, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_35_35_20 hp j hj hq
  simp at hm

theorem pair_36_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_12_4 hp j hj hq
  simp at hm

theorem pair_36_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 36 []).length)
    (hq : (normIsRep.getD 36 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨36, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨36, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_36_36_20 hp j hj hq
  simp at hm

theorem pair_37_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_12_4 hp j hj hq
  simp at hm

theorem pair_37_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 37 []).length)
    (hq : (normIsRep.getD 37 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨37, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨37, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_37_37_20 hp j hj hq
  simp at hm

theorem pair_38_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_12_4 hp j hj hq
  simp at hm

theorem pair_38_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 38 []).length)
    (hq : (normIsRep.getD 38 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨38, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨38, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_38_38_20 hp j hj hq
  simp at hm

theorem pair_39_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_12_4 hp j hj hq
  simp at hm

theorem pair_39_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 39 []).length)
    (hq : (normIsRep.getD 39 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨39, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨39, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_39_39_20 hp j hj hq
  simp at hm

theorem pair_40_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_12_4 hp j hj hq
  simp at hm

theorem pair_40_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 40 []).length)
    (hq : (normIsRep.getD 40 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨40, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨40, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_40_40_20 hp j hj hq
  simp at hm

theorem pair_41_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_12_4 hp j hj hq
  simp at hm

theorem pair_41_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 41 []).length)
    (hq : (normIsRep.getD 41 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨41, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨41, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_41_41_20 hp j hj hq
  simp at hm

theorem pair_42_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_12_4 hp j hj hq
  simp at hm

theorem pair_42_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 42 []).length)
    (hq : (normIsRep.getD 42 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨42, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨42, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_42_42_20 hp j hj hq
  simp at hm

theorem pair_43_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_12_4 hp j hj hq
  simp at hm

theorem pair_43_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 43 []).length)
    (hq : (normIsRep.getD 43 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨43, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨43, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_43_43_20 hp j hj hq
  simp at hm

theorem pair_44_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_12_4 hp j hj hq
  simp at hm

theorem pair_44_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 44 []).length)
    (hq : (normIsRep.getD 44 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨44, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨44, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_44_44_20 hp j hj hq
  simp at hm

theorem pair_45_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_12_4 hp j hj hq
  simp at hm

theorem pair_45_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 45 []).length)
    (hq : (normIsRep.getD 45 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨45, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨45, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_45_45_20 hp j hj hq
  simp at hm

theorem pair_46_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_12_4 hp j hj hq
  simp at hm

theorem pair_46_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 46 []).length)
    (hq : (normIsRep.getD 46 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨46, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨46, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_46_46_20 hp j hj hq
  simp at hm

theorem pair_47_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 47 []).length)
    (hq : (normIsRep.getD 47 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨47, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨47, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_47_12_4 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
