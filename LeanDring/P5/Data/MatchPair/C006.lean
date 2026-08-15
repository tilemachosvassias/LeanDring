/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C021
import LeanDring.P5.Data.MatchLeaf.C022
import LeanDring.P5.Data.MatchLeaf.C023
import LeanDring.P5.Data.MatchLeaf.C024
import LeanDring.P5.Data.MatchLeaf.C025
import LeanDring.P5.Data.MatchLeaf.C026
import LeanDring.P5.Data.MatchLeaf.C027

/-! # Stage-5 per-pair theorems, chunk 5 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_114_114 (p : Nat) (hp : p < (Q2.transData.getD 114 []).length)
    (hrep : (Q2.cosetIsRep.getD 114 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ p hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ p (transLenTr ⟨114, by decide⟩ p hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_114 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_114_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_114_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_114_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_114_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_114_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_114_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_114_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_114_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_114_20 hp j hj hq
  simp at hm

theorem pair_115_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_10_4 hp j hj hq
  simp at hm

theorem pair_115_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_11_4 hp j hj hq
  simp at hm

theorem pair_115_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_12_4 hp j hj hq
  simp at hm

theorem pair_115_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_53_20 hp j hj hq
  simp at hm

theorem pair_115_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_54_20 hp j hj hq
  simp at hm

theorem pair_115_115 (p : Nat) (hp : p < (Q2.transData.getD 115 []).length)
    (hrep : (Q2.cosetIsRep.getD 115 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ p hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ p (transLenTr ⟨115, by decide⟩ p hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_115 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_115_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_115_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_115_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_115_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_115_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_115_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_115_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_115_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_115_115_20 hp j hj hq
  simp at hm

theorem pair_116_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_1_4 hp j hj hq
  simp at hm

theorem pair_116_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_6_4 hp j hj hq
  simp at hm

theorem pair_116_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_7_4 hp j hj hq
  simp at hm

theorem pair_116_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_8_4 hp j hj hq
  simp at hm

theorem pair_116_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_9_4 hp j hj hq
  simp at hm

theorem pair_116_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_10_4 hp j hj hq
  simp at hm

theorem pair_116_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_12_4 hp j hj hq
  simp at hm

theorem pair_116_13 (p : Nat) (hp : p < (Q2.transData.getD 13 []).length)
    (hrep : (Q2.cosetIsRep.getD 13 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ p (transLenTr ⟨13, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_13 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_13_24 hp j hj hq
  simp at hm

theorem pair_116_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_19_20 hp j hj hq
  simp at hm

theorem pair_116_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_24_20 hp j hj hq
  simp at hm

theorem pair_116_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_25_20 hp j hj hq
  simp at hm

theorem pair_116_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_26_20 hp j hj hq
  simp at hm

theorem pair_116_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_27_20 hp j hj hq
  simp at hm

theorem pair_116_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_28_20 hp j hj hq
  simp at hm

theorem pair_116_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_33_20 hp j hj hq
  simp at hm

theorem pair_116_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_38_20 hp j hj hq
  simp at hm

theorem pair_116_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_43_20 hp j hj hq
  simp at hm

theorem pair_116_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_48_20 hp j hj hq
  simp at hm

theorem pair_116_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_53_20 hp j hj hq
  simp at hm

theorem pair_116_55 (p : Nat) (hp : p < (Q2.transData.getD 55 []).length)
    (hrep : (Q2.cosetIsRep.getD 55 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ p (transLenTr ⟨55, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_55 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_55_24 hp j hj hq
  simp at hm

theorem pair_116_56 (p : Nat) (hp : p < (Q2.transData.getD 56 []).length)
    (hrep : (Q2.cosetIsRep.getD 56 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ p (transLenTr ⟨56, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_56 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_56_24 hp j hj hq
  simp at hm

theorem pair_116_57 (p : Nat) (hp : p < (Q2.transData.getD 57 []).length)
    (hrep : (Q2.cosetIsRep.getD 57 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ p (transLenTr ⟨57, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_57 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_57_24 hp j hj hq
  simp at hm

theorem pair_116_58 (p : Nat) (hp : p < (Q2.transData.getD 58 []).length)
    (hrep : (Q2.cosetIsRep.getD 58 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ p (transLenTr ⟨58, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_58 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_58_24 hp j hj hq
  simp at hm

theorem pair_116_59 (p : Nat) (hp : p < (Q2.transData.getD 59 []).length)
    (hrep : (Q2.cosetIsRep.getD 59 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ p (transLenTr ⟨59, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_59 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_59_24 hp j hj hq
  simp at hm

theorem pair_116_80 (p : Nat) (hp : p < (Q2.transData.getD 80 []).length)
    (hrep : (Q2.cosetIsRep.getD 80 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ p (transLenTr ⟨80, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_80 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_80_120 hp j hj hq
  simp at hm

theorem pair_116_90 (p : Nat) (hp : p < (Q2.transData.getD 90 []).length)
    (hrep : (Q2.cosetIsRep.getD 90 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ p (transLenTr ⟨90, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_90 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_90_100 hp j hj hq
  simp at hm

theorem pair_116_95 (p : Nat) (hp : p < (Q2.transData.getD 95 []).length)
    (hrep : (Q2.cosetIsRep.getD 95 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ p (transLenTr ⟨95, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_95 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_95_100 hp j hj hq
  simp at hm

theorem pair_116_100 (p : Nat) (hp : p < (Q2.transData.getD 100 []).length)
    (hrep : (Q2.cosetIsRep.getD 100 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ p (transLenTr ⟨100, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_100 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_100_100 hp j hj hq
  simp at hm

theorem pair_116_105 (p : Nat) (hp : p < (Q2.transData.getD 105 []).length)
    (hrep : (Q2.cosetIsRep.getD 105 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ p (transLenTr ⟨105, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_105 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_105_100 hp j hj hq
  simp at hm

theorem pair_116_110 (p : Nat) (hp : p < (Q2.transData.getD 110 []).length)
    (hrep : (Q2.cosetIsRep.getD 110 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ p (transLenTr ⟨110, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_110 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_110_100 hp j hj hq
  simp at hm

theorem pair_116_116 (p : Nat) (hp : p < (Q2.transData.getD 116 []).length)
    (hrep : (Q2.cosetIsRep.getD 116 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ p hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ p (transLenTr ⟨116, by decide⟩ p hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_116 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_116_116_120 hp j hj hq
  simp at hm

theorem pair_117_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_1_4 hp j hj hq
  simp at hm

theorem pair_117_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_6_4 hp j hj hq
  simp at hm

theorem pair_117_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_7_4 hp j hj hq
  simp at hm

theorem pair_117_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_8_4 hp j hj hq
  simp at hm

theorem pair_117_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_9_4 hp j hj hq
  simp at hm

theorem pair_117_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_10_4 hp j hj hq
  simp at hm

theorem pair_117_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_12_4 hp j hj hq
  simp at hm

theorem pair_117_13 (p : Nat) (hp : p < (Q2.transData.getD 13 []).length)
    (hrep : (Q2.cosetIsRep.getD 13 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ p (transLenTr ⟨13, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_13 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_13_24 hp j hj hq
  simp at hm

theorem pair_117_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_19_20 hp j hj hq
  simp at hm

theorem pair_117_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_24_20 hp j hj hq
  simp at hm

theorem pair_117_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_25_20 hp j hj hq
  simp at hm

theorem pair_117_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_26_20 hp j hj hq
  simp at hm

theorem pair_117_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_27_20 hp j hj hq
  simp at hm

theorem pair_117_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_29_20 hp j hj hq
  simp at hm

theorem pair_117_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_34_20 hp j hj hq
  simp at hm

theorem pair_117_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_39_20 hp j hj hq
  simp at hm

theorem pair_117_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_44_20 hp j hj hq
  simp at hm

theorem pair_117_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_49_20 hp j hj hq
  simp at hm

theorem pair_117_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_53_20 hp j hj hq
  simp at hm

theorem pair_117_60 (p : Nat) (hp : p < (Q2.transData.getD 60 []).length)
    (hrep : (Q2.cosetIsRep.getD 60 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ p (transLenTr ⟨60, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_60 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_60_24 hp j hj hq
  simp at hm

theorem pair_117_61 (p : Nat) (hp : p < (Q2.transData.getD 61 []).length)
    (hrep : (Q2.cosetIsRep.getD 61 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ p (transLenTr ⟨61, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_61 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_61_24 hp j hj hq
  simp at hm

theorem pair_117_62 (p : Nat) (hp : p < (Q2.transData.getD 62 []).length)
    (hrep : (Q2.cosetIsRep.getD 62 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ p (transLenTr ⟨62, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_62 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_62_24 hp j hj hq
  simp at hm

theorem pair_117_63 (p : Nat) (hp : p < (Q2.transData.getD 63 []).length)
    (hrep : (Q2.cosetIsRep.getD 63 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ p (transLenTr ⟨63, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_63 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_63_24 hp j hj hq
  simp at hm

theorem pair_117_64 (p : Nat) (hp : p < (Q2.transData.getD 64 []).length)
    (hrep : (Q2.cosetIsRep.getD 64 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ p (transLenTr ⟨64, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_64 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_64_120 hp j hj hq
  simp at hm

theorem pair_117_80 (p : Nat) (hp : p < (Q2.transData.getD 80 []).length)
    (hrep : (Q2.cosetIsRep.getD 80 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ p (transLenTr ⟨80, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_80 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_80_120 hp j hj hq
  simp at hm

theorem pair_117_91 (p : Nat) (hp : p < (Q2.transData.getD 91 []).length)
    (hrep : (Q2.cosetIsRep.getD 91 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ p (transLenTr ⟨91, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_91 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_91_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_91_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_91_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_91_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_91_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_91_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_91_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_91_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_91_20 hp j hj hq
  simp at hm

theorem pair_117_96 (p : Nat) (hp : p < (Q2.transData.getD 96 []).length)
    (hrep : (Q2.cosetIsRep.getD 96 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ p (transLenTr ⟨96, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_96 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_96_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_96_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_96_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_96_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_96_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_96_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_96_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_96_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_96_20 hp j hj hq
  simp at hm

theorem pair_117_101 (p : Nat) (hp : p < (Q2.transData.getD 101 []).length)
    (hrep : (Q2.cosetIsRep.getD 101 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ p (transLenTr ⟨101, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_101 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_101_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_101_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_101_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_101_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_101_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_101_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_101_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_101_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_101_20 hp j hj hq
  simp at hm

theorem pair_117_106 (p : Nat) (hp : p < (Q2.transData.getD 106 []).length)
    (hrep : (Q2.cosetIsRep.getD 106 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ p (transLenTr ⟨106, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_106 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_106_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_106_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_106_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_106_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_106_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_106_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_106_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_106_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_106_20 hp j hj hq
  simp at hm

theorem pair_117_111 (p : Nat) (hp : p < (Q2.transData.getD 111 []).length)
    (hrep : (Q2.cosetIsRep.getD 111 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ p (transLenTr ⟨111, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_111 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_111_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_111_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_111_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_111_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_111_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_111_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_111_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_111_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_111_20 hp j hj hq
  simp at hm

theorem pair_117_117 (p : Nat) (hp : p < (Q2.transData.getD 117 []).length)
    (hrep : (Q2.cosetIsRep.getD 117 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ p hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ p (transLenTr ⟨117, by decide⟩ p hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_117 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_117_117_120 hp j hj hq
  simp at hm

theorem pair_118_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_1_4 hp j hj hq
  simp at hm

theorem pair_118_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_6_4 hp j hj hq
  simp at hm

theorem pair_118_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_7_4 hp j hj hq
  simp at hm

theorem pair_118_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_8_4 hp j hj hq
  simp at hm

theorem pair_118_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_9_4 hp j hj hq
  simp at hm

theorem pair_118_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_10_4 hp j hj hq
  simp at hm

theorem pair_118_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_12_4 hp j hj hq
  simp at hm

theorem pair_118_13 (p : Nat) (hp : p < (Q2.transData.getD 13 []).length)
    (hrep : (Q2.cosetIsRep.getD 13 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ p (transLenTr ⟨13, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_13 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_13_24 hp j hj hq
  simp at hm

theorem pair_118_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_19_20 hp j hj hq
  simp at hm

theorem pair_118_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_24_20 hp j hj hq
  simp at hm

theorem pair_118_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_25_20 hp j hj hq
  simp at hm

theorem pair_118_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_26_20 hp j hj hq
  simp at hm

theorem pair_118_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_27_20 hp j hj hq
  simp at hm

theorem pair_118_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_30_20 hp j hj hq
  simp at hm

theorem pair_118_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_35_20 hp j hj hq
  simp at hm

theorem pair_118_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_40_20 hp j hj hq
  simp at hm

theorem pair_118_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_45_20 hp j hj hq
  simp at hm

theorem pair_118_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_50_20 hp j hj hq
  simp at hm

theorem pair_118_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_53_20 hp j hj hq
  simp at hm

theorem pair_118_65 (p : Nat) (hp : p < (Q2.transData.getD 65 []).length)
    (hrep : (Q2.cosetIsRep.getD 65 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ p (transLenTr ⟨65, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_65 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_65_24 hp j hj hq
  simp at hm

theorem pair_118_66 (p : Nat) (hp : p < (Q2.transData.getD 66 []).length)
    (hrep : (Q2.cosetIsRep.getD 66 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ p (transLenTr ⟨66, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_66 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_66_24 hp j hj hq
  simp at hm

theorem pair_118_67 (p : Nat) (hp : p < (Q2.transData.getD 67 []).length)
    (hrep : (Q2.cosetIsRep.getD 67 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ p (transLenTr ⟨67, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_67 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_67_120 hp j hj hq
  simp at hm

theorem pair_118_68 (p : Nat) (hp : p < (Q2.transData.getD 68 []).length)
    (hrep : (Q2.cosetIsRep.getD 68 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ p (transLenTr ⟨68, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_68 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_68_24 hp j hj hq
  simp at hm

theorem pair_118_69 (p : Nat) (hp : p < (Q2.transData.getD 69 []).length)
    (hrep : (Q2.cosetIsRep.getD 69 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ p (transLenTr ⟨69, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_69 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_69_24 hp j hj hq
  simp at hm

theorem pair_118_80 (p : Nat) (hp : p < (Q2.transData.getD 80 []).length)
    (hrep : (Q2.cosetIsRep.getD 80 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ p (transLenTr ⟨80, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_80 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_80_120 hp j hj hq
  simp at hm

theorem pair_118_92 (p : Nat) (hp : p < (Q2.transData.getD 92 []).length)
    (hrep : (Q2.cosetIsRep.getD 92 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ p (transLenTr ⟨92, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_92 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_92_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_92_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_92_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_92_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_92_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_92_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_92_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_92_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_92_20 hp j hj hq
  simp at hm

theorem pair_118_97 (p : Nat) (hp : p < (Q2.transData.getD 97 []).length)
    (hrep : (Q2.cosetIsRep.getD 97 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ p (transLenTr ⟨97, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_97 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_97_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_97_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_97_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_97_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_97_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_97_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_97_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_97_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_97_20 hp j hj hq
  simp at hm

theorem pair_118_102 (p : Nat) (hp : p < (Q2.transData.getD 102 []).length)
    (hrep : (Q2.cosetIsRep.getD 102 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ p (transLenTr ⟨102, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_102 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_102_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_102_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_102_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_102_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_102_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_102_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_102_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_102_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_102_20 hp j hj hq
  simp at hm

theorem pair_118_107 (p : Nat) (hp : p < (Q2.transData.getD 107 []).length)
    (hrep : (Q2.cosetIsRep.getD 107 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ p (transLenTr ⟨107, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_107 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_107_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_107_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_107_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_107_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_107_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_107_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_107_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_107_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_107_20 hp j hj hq
  simp at hm

theorem pair_118_112 (p : Nat) (hp : p < (Q2.transData.getD 112 []).length)
    (hrep : (Q2.cosetIsRep.getD 112 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ p (transLenTr ⟨112, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_112 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_112_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_112_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_112_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_112_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_112_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_112_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_112_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_112_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_112_20 hp j hj hq
  simp at hm

theorem pair_118_118 (p : Nat) (hp : p < (Q2.transData.getD 118 []).length)
    (hrep : (Q2.cosetIsRep.getD 118 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ p hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ p (transLenTr ⟨118, by decide⟩ p hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_118 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_118_118_120 hp j hj hq
  simp at hm

theorem pair_119_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_1_4 hp j hj hq
  simp at hm

theorem pair_119_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_6_4 hp j hj hq
  simp at hm

theorem pair_119_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_7_4 hp j hj hq
  simp at hm

theorem pair_119_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_8_4 hp j hj hq
  simp at hm

theorem pair_119_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_9_4 hp j hj hq
  simp at hm

theorem pair_119_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_10_4 hp j hj hq
  simp at hm

theorem pair_119_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_12_4 hp j hj hq
  simp at hm

theorem pair_119_13 (p : Nat) (hp : p < (Q2.transData.getD 13 []).length)
    (hrep : (Q2.cosetIsRep.getD 13 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ p (transLenTr ⟨13, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_13 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_13_24 hp j hj hq
  simp at hm

theorem pair_119_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_19_20 hp j hj hq
  simp at hm

theorem pair_119_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_24_20 hp j hj hq
  simp at hm

theorem pair_119_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_25_20 hp j hj hq
  simp at hm

theorem pair_119_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_26_20 hp j hj hq
  simp at hm

theorem pair_119_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_27_20 hp j hj hq
  simp at hm

theorem pair_119_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_31_20 hp j hj hq
  simp at hm

theorem pair_119_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_36_20 hp j hj hq
  simp at hm

theorem pair_119_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_41_20 hp j hj hq
  simp at hm

theorem pair_119_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_46_20 hp j hj hq
  simp at hm

theorem pair_119_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_51_20 hp j hj hq
  simp at hm

theorem pair_119_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_53_20 hp j hj hq
  simp at hm

theorem pair_119_70 (p : Nat) (hp : p < (Q2.transData.getD 70 []).length)
    (hrep : (Q2.cosetIsRep.getD 70 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ p (transLenTr ⟨70, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_70 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_70_24 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
