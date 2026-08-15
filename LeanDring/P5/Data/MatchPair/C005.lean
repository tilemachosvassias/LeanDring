/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C018
import LeanDring.P5.Data.MatchLeaf.C019
import LeanDring.P5.Data.MatchLeaf.C020
import LeanDring.P5.Data.MatchLeaf.C021

/-! # Stage-5 per-pair theorems, chunk 4 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_90_90 (p : Nat) (hp : p < (Q2.transData.getD 90 []).length)
    (hrep : (Q2.cosetIsRep.getD 90 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ p hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ p (transLenTr ⟨90, by decide⟩ p hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_90 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_90_90_100 hp j hj hq
  simp at hm

theorem pair_91_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_10_4 hp j hj hq
  simp at hm

theorem pair_91_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_12_4 hp j hj hq
  simp at hm

theorem pair_91_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_29_20 hp j hj hq
  simp at hm

theorem pair_91_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_53_20 hp j hj hq
  simp at hm

theorem pair_91_91 (p : Nat) (hp : p < (Q2.transData.getD 91 []).length)
    (hrep : (Q2.cosetIsRep.getD 91 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ p hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ p (transLenTr ⟨91, by decide⟩ p hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_91 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_91_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_91_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_91_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_91_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_91_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_91_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_91_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_91_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_91_91_20 hp j hj hq
  simp at hm

theorem pair_92_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_10_4 hp j hj hq
  simp at hm

theorem pair_92_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_12_4 hp j hj hq
  simp at hm

theorem pair_92_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_30_20 hp j hj hq
  simp at hm

theorem pair_92_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_53_20 hp j hj hq
  simp at hm

theorem pair_92_92 (p : Nat) (hp : p < (Q2.transData.getD 92 []).length)
    (hrep : (Q2.cosetIsRep.getD 92 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ p hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ p (transLenTr ⟨92, by decide⟩ p hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_92 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_92_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_92_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_92_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_92_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_92_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_92_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_92_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_92_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_92_92_20 hp j hj hq
  simp at hm

theorem pair_93_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_10_4 hp j hj hq
  simp at hm

theorem pair_93_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_12_4 hp j hj hq
  simp at hm

theorem pair_93_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_31_20 hp j hj hq
  simp at hm

theorem pair_93_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_53_20 hp j hj hq
  simp at hm

theorem pair_93_93 (p : Nat) (hp : p < (Q2.transData.getD 93 []).length)
    (hrep : (Q2.cosetIsRep.getD 93 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ p hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ p (transLenTr ⟨93, by decide⟩ p hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_93 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_93_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_93_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_93_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_93_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_93_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_93_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_93_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_93_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_93_93_20 hp j hj hq
  simp at hm

theorem pair_94_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_10_4 hp j hj hq
  simp at hm

theorem pair_94_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_12_4 hp j hj hq
  simp at hm

theorem pair_94_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_32_20 hp j hj hq
  simp at hm

theorem pair_94_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_53_20 hp j hj hq
  simp at hm

theorem pair_94_94 (p : Nat) (hp : p < (Q2.transData.getD 94 []).length)
    (hrep : (Q2.cosetIsRep.getD 94 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ p hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ p (transLenTr ⟨94, by decide⟩ p hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_94 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_94_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_94_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_94_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_94_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_94_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_94_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_94_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_94_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_94_94_20 hp j hj hq
  simp at hm

theorem pair_95_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_10_4 hp j hj hq
  simp at hm

theorem pair_95_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_12_4 hp j hj hq
  simp at hm

theorem pair_95_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_33_20 hp j hj hq
  simp at hm

theorem pair_95_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_53_20 hp j hj hq
  simp at hm

theorem pair_95_95 (p : Nat) (hp : p < (Q2.transData.getD 95 []).length)
    (hrep : (Q2.cosetIsRep.getD 95 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ p hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ p (transLenTr ⟨95, by decide⟩ p hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_95 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_95_95_100 hp j hj hq
  simp at hm

theorem pair_96_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_10_4 hp j hj hq
  simp at hm

theorem pair_96_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_12_4 hp j hj hq
  simp at hm

theorem pair_96_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_34_20 hp j hj hq
  simp at hm

theorem pair_96_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_53_20 hp j hj hq
  simp at hm

theorem pair_96_96 (p : Nat) (hp : p < (Q2.transData.getD 96 []).length)
    (hrep : (Q2.cosetIsRep.getD 96 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 96 []).length)
    (hq : (normIsRep.getD 96 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ p hp)
        (rowE2 (⟨96, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ p (transLenTr ⟨96, by decide⟩ p hp))
        (rowE1 (⟨96, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_96 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_96_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_96_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_96_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_96_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_96_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_96_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_96_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_96_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_96_96_20 hp j hj hq
  simp at hm

theorem pair_97_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_10_4 hp j hj hq
  simp at hm

theorem pair_97_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_12_4 hp j hj hq
  simp at hm

theorem pair_97_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_35_20 hp j hj hq
  simp at hm

theorem pair_97_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_53_20 hp j hj hq
  simp at hm

theorem pair_97_97 (p : Nat) (hp : p < (Q2.transData.getD 97 []).length)
    (hrep : (Q2.cosetIsRep.getD 97 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 97 []).length)
    (hq : (normIsRep.getD 97 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ p hp)
        (rowE2 (⟨97, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ p (transLenTr ⟨97, by decide⟩ p hp))
        (rowE1 (⟨97, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_97 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_97_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_97_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_97_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_97_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_97_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_97_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_97_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_97_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_97_97_20 hp j hj hq
  simp at hm

theorem pair_98_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_10_4 hp j hj hq
  simp at hm

theorem pair_98_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_12_4 hp j hj hq
  simp at hm

theorem pair_98_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_36_20 hp j hj hq
  simp at hm

theorem pair_98_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_53_20 hp j hj hq
  simp at hm

theorem pair_98_98 (p : Nat) (hp : p < (Q2.transData.getD 98 []).length)
    (hrep : (Q2.cosetIsRep.getD 98 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 98 []).length)
    (hq : (normIsRep.getD 98 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ p hp)
        (rowE2 (⟨98, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ p (transLenTr ⟨98, by decide⟩ p hp))
        (rowE1 (⟨98, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_98 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_98_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_98_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_98_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_98_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_98_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_98_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_98_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_98_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_98_98_20 hp j hj hq
  simp at hm

theorem pair_99_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_10_4 hp j hj hq
  simp at hm

theorem pair_99_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_12_4 hp j hj hq
  simp at hm

theorem pair_99_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_37_20 hp j hj hq
  simp at hm

theorem pair_99_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_53_20 hp j hj hq
  simp at hm

theorem pair_99_99 (p : Nat) (hp : p < (Q2.transData.getD 99 []).length)
    (hrep : (Q2.cosetIsRep.getD 99 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 99 []).length)
    (hq : (normIsRep.getD 99 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ p hp)
        (rowE2 (⟨99, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ p (transLenTr ⟨99, by decide⟩ p hp))
        (rowE1 (⟨99, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_99 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_99_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_99_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_99_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_99_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_99_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_99_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_99_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_99_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_99_99_20 hp j hj hq
  simp at hm

theorem pair_100_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_10_4 hp j hj hq
  simp at hm

theorem pair_100_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_12_4 hp j hj hq
  simp at hm

theorem pair_100_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_38_20 hp j hj hq
  simp at hm

theorem pair_100_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_53_20 hp j hj hq
  simp at hm

theorem pair_100_100 (p : Nat) (hp : p < (Q2.transData.getD 100 []).length)
    (hrep : (Q2.cosetIsRep.getD 100 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 100 []).length)
    (hq : (normIsRep.getD 100 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ p hp)
        (rowE2 (⟨100, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ p (transLenTr ⟨100, by decide⟩ p hp))
        (rowE1 (⟨100, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_100 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_100_100_100 hp j hj hq
  simp at hm

theorem pair_101_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_10_4 hp j hj hq
  simp at hm

theorem pair_101_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_12_4 hp j hj hq
  simp at hm

theorem pair_101_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_39_20 hp j hj hq
  simp at hm

theorem pair_101_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_53_20 hp j hj hq
  simp at hm

theorem pair_101_101 (p : Nat) (hp : p < (Q2.transData.getD 101 []).length)
    (hrep : (Q2.cosetIsRep.getD 101 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 101 []).length)
    (hq : (normIsRep.getD 101 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ p hp)
        (rowE2 (⟨101, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ p (transLenTr ⟨101, by decide⟩ p hp))
        (rowE1 (⟨101, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_101 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_101_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_101_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_101_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_101_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_101_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_101_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_101_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_101_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_101_101_20 hp j hj hq
  simp at hm

theorem pair_102_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_10_4 hp j hj hq
  simp at hm

theorem pair_102_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_12_4 hp j hj hq
  simp at hm

theorem pair_102_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_40_20 hp j hj hq
  simp at hm

theorem pair_102_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_53_20 hp j hj hq
  simp at hm

theorem pair_102_102 (p : Nat) (hp : p < (Q2.transData.getD 102 []).length)
    (hrep : (Q2.cosetIsRep.getD 102 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 102 []).length)
    (hq : (normIsRep.getD 102 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ p hp)
        (rowE2 (⟨102, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ p (transLenTr ⟨102, by decide⟩ p hp))
        (rowE1 (⟨102, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_102 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_102_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_102_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_102_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_102_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_102_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_102_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_102_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_102_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_102_102_20 hp j hj hq
  simp at hm

theorem pair_103_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_10_4 hp j hj hq
  simp at hm

theorem pair_103_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_12_4 hp j hj hq
  simp at hm

theorem pair_103_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_41_20 hp j hj hq
  simp at hm

theorem pair_103_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_53_20 hp j hj hq
  simp at hm

theorem pair_103_103 (p : Nat) (hp : p < (Q2.transData.getD 103 []).length)
    (hrep : (Q2.cosetIsRep.getD 103 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 103 []).length)
    (hq : (normIsRep.getD 103 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ p hp)
        (rowE2 (⟨103, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ p (transLenTr ⟨103, by decide⟩ p hp))
        (rowE1 (⟨103, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_103 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_103_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_103_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_103_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_103_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_103_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_103_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_103_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_103_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_103_103_20 hp j hj hq
  simp at hm

theorem pair_104_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_10_4 hp j hj hq
  simp at hm

theorem pair_104_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_12_4 hp j hj hq
  simp at hm

theorem pair_104_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_42_20 hp j hj hq
  simp at hm

theorem pair_104_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_53_20 hp j hj hq
  simp at hm

theorem pair_104_104 (p : Nat) (hp : p < (Q2.transData.getD 104 []).length)
    (hrep : (Q2.cosetIsRep.getD 104 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 104 []).length)
    (hq : (normIsRep.getD 104 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ p hp)
        (rowE2 (⟨104, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ p (transLenTr ⟨104, by decide⟩ p hp))
        (rowE1 (⟨104, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_104 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_104_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_104_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_104_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_104_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_104_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_104_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_104_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_104_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_104_104_20 hp j hj hq
  simp at hm

theorem pair_105_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_10_4 hp j hj hq
  simp at hm

theorem pair_105_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_12_4 hp j hj hq
  simp at hm

theorem pair_105_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_43_20 hp j hj hq
  simp at hm

theorem pair_105_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_53_20 hp j hj hq
  simp at hm

theorem pair_105_105 (p : Nat) (hp : p < (Q2.transData.getD 105 []).length)
    (hrep : (Q2.cosetIsRep.getD 105 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 105 []).length)
    (hq : (normIsRep.getD 105 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ p hp)
        (rowE2 (⟨105, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ p (transLenTr ⟨105, by decide⟩ p hp))
        (rowE1 (⟨105, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_105 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_105_105_100 hp j hj hq
  simp at hm

theorem pair_106_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_10_4 hp j hj hq
  simp at hm

theorem pair_106_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_12_4 hp j hj hq
  simp at hm

theorem pair_106_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_44_20 hp j hj hq
  simp at hm

theorem pair_106_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_53_20 hp j hj hq
  simp at hm

theorem pair_106_106 (p : Nat) (hp : p < (Q2.transData.getD 106 []).length)
    (hrep : (Q2.cosetIsRep.getD 106 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 106 []).length)
    (hq : (normIsRep.getD 106 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ p hp)
        (rowE2 (⟨106, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ p (transLenTr ⟨106, by decide⟩ p hp))
        (rowE1 (⟨106, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_106 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_106_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_106_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_106_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_106_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_106_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_106_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_106_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_106_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_106_106_20 hp j hj hq
  simp at hm

theorem pair_107_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_10_4 hp j hj hq
  simp at hm

theorem pair_107_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_12_4 hp j hj hq
  simp at hm

theorem pair_107_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_45_20 hp j hj hq
  simp at hm

theorem pair_107_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_53_20 hp j hj hq
  simp at hm

theorem pair_107_107 (p : Nat) (hp : p < (Q2.transData.getD 107 []).length)
    (hrep : (Q2.cosetIsRep.getD 107 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 107 []).length)
    (hq : (normIsRep.getD 107 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ p hp)
        (rowE2 (⟨107, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ p (transLenTr ⟨107, by decide⟩ p hp))
        (rowE1 (⟨107, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_107 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_107_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_107_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_107_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_107_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_107_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_107_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_107_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_107_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_107_107_20 hp j hj hq
  simp at hm

theorem pair_108_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_10_4 hp j hj hq
  simp at hm

theorem pair_108_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_12_4 hp j hj hq
  simp at hm

theorem pair_108_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_46_20 hp j hj hq
  simp at hm

theorem pair_108_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_53_20 hp j hj hq
  simp at hm

theorem pair_108_108 (p : Nat) (hp : p < (Q2.transData.getD 108 []).length)
    (hrep : (Q2.cosetIsRep.getD 108 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 108 []).length)
    (hq : (normIsRep.getD 108 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ p hp)
        (rowE2 (⟨108, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ p (transLenTr ⟨108, by decide⟩ p hp))
        (rowE1 (⟨108, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_108 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_108_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_108_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_108_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_108_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_108_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_108_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_108_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_108_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_108_108_20 hp j hj hq
  simp at hm

theorem pair_109_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_10_4 hp j hj hq
  simp at hm

theorem pair_109_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_12_4 hp j hj hq
  simp at hm

theorem pair_109_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_47_20 hp j hj hq
  simp at hm

theorem pair_109_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_53_20 hp j hj hq
  simp at hm

theorem pair_109_109 (p : Nat) (hp : p < (Q2.transData.getD 109 []).length)
    (hrep : (Q2.cosetIsRep.getD 109 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ p hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ p (transLenTr ⟨109, by decide⟩ p hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_109 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_109_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_109_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_109_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_109_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_109_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_109_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_109_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_109_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_109_109_20 hp j hj hq
  simp at hm

theorem pair_110_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_10_4 hp j hj hq
  simp at hm

theorem pair_110_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_12_4 hp j hj hq
  simp at hm

theorem pair_110_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_48_20 hp j hj hq
  simp at hm

theorem pair_110_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_53_20 hp j hj hq
  simp at hm

theorem pair_110_110 (p : Nat) (hp : p < (Q2.transData.getD 110 []).length)
    (hrep : (Q2.cosetIsRep.getD 110 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ p hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ p (transLenTr ⟨110, by decide⟩ p hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_110 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_110_110_100 hp j hj hq
  simp at hm

theorem pair_111_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_10_4 hp j hj hq
  simp at hm

theorem pair_111_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_12_4 hp j hj hq
  simp at hm

theorem pair_111_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_49_20 hp j hj hq
  simp at hm

theorem pair_111_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_53_20 hp j hj hq
  simp at hm

theorem pair_111_111 (p : Nat) (hp : p < (Q2.transData.getD 111 []).length)
    (hrep : (Q2.cosetIsRep.getD 111 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ p hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ p (transLenTr ⟨111, by decide⟩ p hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_111 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_111_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_111_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_111_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_111_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_111_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_111_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_111_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_111_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_111_111_20 hp j hj hq
  simp at hm

theorem pair_112_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_10_4 hp j hj hq
  simp at hm

theorem pair_112_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_12_4 hp j hj hq
  simp at hm

theorem pair_112_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_50_20 hp j hj hq
  simp at hm

theorem pair_112_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_53_20 hp j hj hq
  simp at hm

theorem pair_112_112 (p : Nat) (hp : p < (Q2.transData.getD 112 []).length)
    (hrep : (Q2.cosetIsRep.getD 112 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ p hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ p (transLenTr ⟨112, by decide⟩ p hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_112 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_112_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_112_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_112_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_112_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_112_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_112_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_112_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_112_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_112_112_20 hp j hj hq
  simp at hm

theorem pair_113_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_10_4 hp j hj hq
  simp at hm

theorem pair_113_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_12_4 hp j hj hq
  simp at hm

theorem pair_113_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_51_20 hp j hj hq
  simp at hm

theorem pair_113_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_53_20 hp j hj hq
  simp at hm

theorem pair_113_113 (p : Nat) (hp : p < (Q2.transData.getD 113 []).length)
    (hrep : (Q2.cosetIsRep.getD 113 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ p hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ p (transLenTr ⟨113, by decide⟩ p hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_113 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_113_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_113_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_113_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_113_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_113_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_113_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_113_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_113_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_113_113_20 hp j hj hq
  simp at hm

theorem pair_114_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_10_4 hp j hj hq
  simp at hm

theorem pair_114_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_12_4 hp j hj hq
  simp at hm

theorem pair_114_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_52_20 hp j hj hq
  simp at hm

theorem pair_114_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_114_53_20 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
