/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C027
import LeanDring.P5.Data.MatchLeaf.C028
import LeanDring.P5.Data.MatchLeaf.C029
import LeanDring.P5.Data.MatchLeaf.C030
import LeanDring.P5.Data.MatchLeaf.C031
import LeanDring.P5.Data.MatchLeaf.C032
import LeanDring.P5.Data.MatchLeaf.C033

/-! # Stage-5 per-pair theorems, chunk 6 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_119_71 (p : Nat) (hp : p < (Q2.transData.getD 71 []).length)
    (hrep : (Q2.cosetIsRep.getD 71 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ p (transLenTr ⟨71, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_71 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_71_24 hp j hj hq
  simp at hm

theorem pair_119_72 (p : Nat) (hp : p < (Q2.transData.getD 72 []).length)
    (hrep : (Q2.cosetIsRep.getD 72 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ p (transLenTr ⟨72, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_72 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_72_24 hp j hj hq
  simp at hm

theorem pair_119_73 (p : Nat) (hp : p < (Q2.transData.getD 73 []).length)
    (hrep : (Q2.cosetIsRep.getD 73 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ p (transLenTr ⟨73, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_73 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_73_120 hp j hj hq
  simp at hm

theorem pair_119_74 (p : Nat) (hp : p < (Q2.transData.getD 74 []).length)
    (hrep : (Q2.cosetIsRep.getD 74 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ p (transLenTr ⟨74, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_74 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_74_24 hp j hj hq
  simp at hm

theorem pair_119_80 (p : Nat) (hp : p < (Q2.transData.getD 80 []).length)
    (hrep : (Q2.cosetIsRep.getD 80 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ p (transLenTr ⟨80, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_80 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_80_120 hp j hj hq
  simp at hm

theorem pair_119_93 (p : Nat) (hp : p < (Q2.transData.getD 93 []).length)
    (hrep : (Q2.cosetIsRep.getD 93 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ p (transLenTr ⟨93, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_93 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_93_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_93_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_93_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_93_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_93_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_93_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_93_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_93_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_93_20 hp j hj hq
  simp at hm

theorem pair_119_98 (p : Nat) (hp : p < (Q2.transData.getD 98 []).length)
    (hrep : (Q2.cosetIsRep.getD 98 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ p (transLenTr ⟨98, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_98 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_98_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_98_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_98_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_98_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_98_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_98_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_98_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_98_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_98_20 hp j hj hq
  simp at hm

theorem pair_119_103 (p : Nat) (hp : p < (Q2.transData.getD 103 []).length)
    (hrep : (Q2.cosetIsRep.getD 103 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ p (transLenTr ⟨103, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_103 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_103_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_103_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_103_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_103_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_103_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_103_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_103_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_103_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_103_20 hp j hj hq
  simp at hm

theorem pair_119_108 (p : Nat) (hp : p < (Q2.transData.getD 108 []).length)
    (hrep : (Q2.cosetIsRep.getD 108 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ p (transLenTr ⟨108, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_108 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_108_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_108_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_108_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_108_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_108_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_108_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_108_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_108_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_108_20 hp j hj hq
  simp at hm

theorem pair_119_113 (p : Nat) (hp : p < (Q2.transData.getD 113 []).length)
    (hrep : (Q2.cosetIsRep.getD 113 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ p (transLenTr ⟨113, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_113 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_113_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_113_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_113_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_113_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_113_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_113_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_113_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_113_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_113_20 hp j hj hq
  simp at hm

theorem pair_119_119 (p : Nat) (hp : p < (Q2.transData.getD 119 []).length)
    (hrep : (Q2.cosetIsRep.getD 119 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ p hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ p (transLenTr ⟨119, by decide⟩ p hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_119 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_119_119_120 hp j hj hq
  simp at hm

theorem pair_120_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_1_4 hp j hj hq
  simp at hm

theorem pair_120_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_6_4 hp j hj hq
  simp at hm

theorem pair_120_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_7_4 hp j hj hq
  simp at hm

theorem pair_120_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_8_4 hp j hj hq
  simp at hm

theorem pair_120_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_9_4 hp j hj hq
  simp at hm

theorem pair_120_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_10_4 hp j hj hq
  simp at hm

theorem pair_120_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_12_4 hp j hj hq
  simp at hm

theorem pair_120_13 (p : Nat) (hp : p < (Q2.transData.getD 13 []).length)
    (hrep : (Q2.cosetIsRep.getD 13 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ p (transLenTr ⟨13, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_13 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_13_24 hp j hj hq
  simp at hm

theorem pair_120_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_19_20 hp j hj hq
  simp at hm

theorem pair_120_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_24_20 hp j hj hq
  simp at hm

theorem pair_120_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_25_20 hp j hj hq
  simp at hm

theorem pair_120_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_26_20 hp j hj hq
  simp at hm

theorem pair_120_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_27_20 hp j hj hq
  simp at hm

theorem pair_120_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_32_20 hp j hj hq
  simp at hm

theorem pair_120_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_37_20 hp j hj hq
  simp at hm

theorem pair_120_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_42_20 hp j hj hq
  simp at hm

theorem pair_120_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_47_20 hp j hj hq
  simp at hm

theorem pair_120_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_52_20 hp j hj hq
  simp at hm

theorem pair_120_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_53_20 hp j hj hq
  simp at hm

theorem pair_120_75 (p : Nat) (hp : p < (Q2.transData.getD 75 []).length)
    (hrep : (Q2.cosetIsRep.getD 75 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ p (transLenTr ⟨75, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_75 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_75_24 hp j hj hq
  simp at hm

theorem pair_120_76 (p : Nat) (hp : p < (Q2.transData.getD 76 []).length)
    (hrep : (Q2.cosetIsRep.getD 76 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ p (transLenTr ⟨76, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_76 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_76_120 hp j hj hq
  simp at hm

theorem pair_120_77 (p : Nat) (hp : p < (Q2.transData.getD 77 []).length)
    (hrep : (Q2.cosetIsRep.getD 77 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ p (transLenTr ⟨77, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_77 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_77_24 hp j hj hq
  simp at hm

theorem pair_120_78 (p : Nat) (hp : p < (Q2.transData.getD 78 []).length)
    (hrep : (Q2.cosetIsRep.getD 78 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ p (transLenTr ⟨78, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_78 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_78_24 hp j hj hq
  simp at hm

theorem pair_120_79 (p : Nat) (hp : p < (Q2.transData.getD 79 []).length)
    (hrep : (Q2.cosetIsRep.getD 79 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ p (transLenTr ⟨79, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_79 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_79_24 hp j hj hq
  simp at hm

theorem pair_120_80 (p : Nat) (hp : p < (Q2.transData.getD 80 []).length)
    (hrep : (Q2.cosetIsRep.getD 80 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ p (transLenTr ⟨80, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_80 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_80_120 hp j hj hq
  simp at hm

theorem pair_120_94 (p : Nat) (hp : p < (Q2.transData.getD 94 []).length)
    (hrep : (Q2.cosetIsRep.getD 94 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ p (transLenTr ⟨94, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_94 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_94_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_94_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_94_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_94_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_94_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_94_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_94_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_94_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_94_20 hp j hj hq
  simp at hm

theorem pair_120_99 (p : Nat) (hp : p < (Q2.transData.getD 99 []).length)
    (hrep : (Q2.cosetIsRep.getD 99 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ p (transLenTr ⟨99, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_99 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_99_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_99_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_99_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_99_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_99_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_99_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_99_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_99_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_99_20 hp j hj hq
  simp at hm

theorem pair_120_104 (p : Nat) (hp : p < (Q2.transData.getD 104 []).length)
    (hrep : (Q2.cosetIsRep.getD 104 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ p (transLenTr ⟨104, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_104 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_104_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_104_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_104_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_104_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_104_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_104_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_104_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_104_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_104_20 hp j hj hq
  simp at hm

theorem pair_120_109 (p : Nat) (hp : p < (Q2.transData.getD 109 []).length)
    (hrep : (Q2.cosetIsRep.getD 109 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ p (transLenTr ⟨109, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_109 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_109_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_109_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_109_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_109_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_109_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_109_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_109_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_109_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_109_20 hp j hj hq
  simp at hm

theorem pair_120_114 (p : Nat) (hp : p < (Q2.transData.getD 114 []).length)
    (hrep : (Q2.cosetIsRep.getD 114 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ p (transLenTr ⟨114, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_114 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_114_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_114_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_114_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_114_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_114_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_114_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_114_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_114_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_114_20 hp j hj hq
  simp at hm

theorem pair_120_120 (p : Nat) (hp : p < (Q2.transData.getD 120 []).length)
    (hrep : (Q2.cosetIsRep.getD 120 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ p hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ p (transLenTr ⟨120, by decide⟩ p hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_120 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_120_120_120 hp j hj hq
  simp at hm

theorem pair_121_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_2_4 hp j hj hq
  simp at hm

theorem pair_121_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_10_4 hp j hj hq
  simp at hm

theorem pair_121_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_12_4 hp j hj hq
  simp at hm

theorem pair_121_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_20_20 hp j hj hq
  simp at hm

theorem pair_121_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_32_20 hp j hj hq
  simp at hm

theorem pair_121_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_35_20 hp j hj hq
  simp at hm

theorem pair_121_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_41_20 hp j hj hq
  simp at hm

theorem pair_121_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_44_20 hp j hj hq
  simp at hm

theorem pair_121_48 (p : Nat) (hp : p < (Q2.transData.getD 48 []).length)
    (hrep : (Q2.cosetIsRep.getD 48 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ p (transLenTr ⟨48, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_48 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_48_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_48_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_48_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_48_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_48_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_48_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_48_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_48_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_48_20 hp j hj hq
  simp at hm

theorem pair_121_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_53_20 hp j hj hq
  simp at hm

theorem pair_121_81 (p : Nat) (hp : p < (Q2.transData.getD 81 []).length)
    (hrep : (Q2.cosetIsRep.getD 81 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ p (transLenTr ⟨81, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_81 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_81_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_81_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_81_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_81_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_81_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_81_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_81_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_81_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_81_20 hp j hj hq
  simp at hm

theorem pair_121_94 (p : Nat) (hp : p < (Q2.transData.getD 94 []).length)
    (hrep : (Q2.cosetIsRep.getD 94 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ p (transLenTr ⟨94, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_94 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_94_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_94_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_94_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_94_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_94_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_94_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_94_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_94_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_94_20 hp j hj hq
  simp at hm

theorem pair_121_97 (p : Nat) (hp : p < (Q2.transData.getD 97 []).length)
    (hrep : (Q2.cosetIsRep.getD 97 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ p (transLenTr ⟨97, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_97 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_97_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_97_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_97_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_97_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_97_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_97_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_97_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_97_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_97_20 hp j hj hq
  simp at hm

theorem pair_121_103 (p : Nat) (hp : p < (Q2.transData.getD 103 []).length)
    (hrep : (Q2.cosetIsRep.getD 103 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ p (transLenTr ⟨103, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_103 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_103_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_103_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_103_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_103_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_103_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_103_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_103_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_103_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_103_20 hp j hj hq
  simp at hm

theorem pair_121_106 (p : Nat) (hp : p < (Q2.transData.getD 106 []).length)
    (hrep : (Q2.cosetIsRep.getD 106 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ p (transLenTr ⟨106, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_106 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_106_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_106_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_106_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_106_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_106_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_106_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_106_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_106_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_106_20 hp j hj hq
  simp at hm

theorem pair_121_110 (p : Nat) (hp : p < (Q2.transData.getD 110 []).length)
    (hrep : (Q2.cosetIsRep.getD 110 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ p (transLenTr ⟨110, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_110 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_110_100 hp j hj hq
  simp at hm

theorem pair_121_121 (p : Nat) (hp : p < (Q2.transData.getD 121 []).length)
    (hrep : (Q2.cosetIsRep.getD 121 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ p hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ p (transLenTr ⟨121, by decide⟩ p hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_121 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_121_121_24 hp j hj hq
  simp at hm

theorem pair_122_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_2_4 hp j hj hq
  simp at hm

theorem pair_122_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_10_4 hp j hj hq
  simp at hm

theorem pair_122_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_12_4 hp j hj hq
  simp at hm

theorem pair_122_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_20_20 hp j hj hq
  simp at hm

theorem pair_122_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_28_20 hp j hj hq
  simp at hm

theorem pair_122_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_36_20 hp j hj hq
  simp at hm

theorem pair_122_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_42_20 hp j hj hq
  simp at hm

theorem pair_122_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_45_20 hp j hj hq
  simp at hm

theorem pair_122_49 (p : Nat) (hp : p < (Q2.transData.getD 49 []).length)
    (hrep : (Q2.cosetIsRep.getD 49 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ p (transLenTr ⟨49, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_49 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_49_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_49_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_49_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_49_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_49_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_49_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_49_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_49_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_49_20 hp j hj hq
  simp at hm

theorem pair_122_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_53_20 hp j hj hq
  simp at hm

theorem pair_122_81 (p : Nat) (hp : p < (Q2.transData.getD 81 []).length)
    (hrep : (Q2.cosetIsRep.getD 81 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ p (transLenTr ⟨81, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_81 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_81_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_81_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_81_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_81_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_81_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_81_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_81_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_81_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_81_20 hp j hj hq
  simp at hm

theorem pair_122_90 (p : Nat) (hp : p < (Q2.transData.getD 90 []).length)
    (hrep : (Q2.cosetIsRep.getD 90 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ p (transLenTr ⟨90, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_90 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_90_100 hp j hj hq
  simp at hm

theorem pair_122_98 (p : Nat) (hp : p < (Q2.transData.getD 98 []).length)
    (hrep : (Q2.cosetIsRep.getD 98 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ p (transLenTr ⟨98, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_98 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_98_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_98_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_98_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_98_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_98_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_98_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_98_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_98_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_98_20 hp j hj hq
  simp at hm

theorem pair_122_104 (p : Nat) (hp : p < (Q2.transData.getD 104 []).length)
    (hrep : (Q2.cosetIsRep.getD 104 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ p (transLenTr ⟨104, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_104 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_104_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_104_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_104_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_104_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_104_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_104_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_104_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_104_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_104_20 hp j hj hq
  simp at hm

theorem pair_122_107 (p : Nat) (hp : p < (Q2.transData.getD 107 []).length)
    (hrep : (Q2.cosetIsRep.getD 107 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ p (transLenTr ⟨107, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_107 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_107_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_107_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_107_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_107_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_107_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_107_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_107_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_107_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_107_20 hp j hj hq
  simp at hm

theorem pair_122_111 (p : Nat) (hp : p < (Q2.transData.getD 111 []).length)
    (hrep : (Q2.cosetIsRep.getD 111 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ p (transLenTr ⟨111, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_111 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_111_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_111_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_111_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_111_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_111_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_111_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_111_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_111_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_111_20 hp j hj hq
  simp at hm

theorem pair_122_122 (p : Nat) (hp : p < (Q2.transData.getD 122 []).length)
    (hrep : (Q2.cosetIsRep.getD 122 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 122 []).length)
    (hq : (normIsRep.getD 122 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ p hp)
        (rowE2 (⟨122, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ p (transLenTr ⟨122, by decide⟩ p hp))
        (rowE1 (⟨122, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_122 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_122_122_24 hp j hj hq
  simp at hm

theorem pair_123_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_2_4 hp j hj hq
  simp at hm

theorem pair_123_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_10_4 hp j hj hq
  simp at hm

theorem pair_123_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_12_4 hp j hj hq
  simp at hm

theorem pair_123_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_20_20 hp j hj hq
  simp at hm

theorem pair_123_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_29_20 hp j hj hq
  simp at hm

theorem pair_123_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_37_20 hp j hj hq
  simp at hm

theorem pair_123_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_38_20 hp j hj hq
  simp at hm

theorem pair_123_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_46_20 hp j hj hq
  simp at hm

theorem pair_123_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_50_20 hp j hj hq
  simp at hm

theorem pair_123_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_53_20 hp j hj hq
  simp at hm

theorem pair_123_81 (p : Nat) (hp : p < (Q2.transData.getD 81 []).length)
    (hrep : (Q2.cosetIsRep.getD 81 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ p (transLenTr ⟨81, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_81 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_81_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_81_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_81_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_81_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_81_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_81_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_81_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_81_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_81_20 hp j hj hq
  simp at hm

theorem pair_123_91 (p : Nat) (hp : p < (Q2.transData.getD 91 []).length)
    (hrep : (Q2.cosetIsRep.getD 91 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ p (transLenTr ⟨91, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_91 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_91_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_91_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_91_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_91_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_91_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_91_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_91_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_91_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_91_20 hp j hj hq
  simp at hm

theorem pair_123_99 (p : Nat) (hp : p < (Q2.transData.getD 99 []).length)
    (hrep : (Q2.cosetIsRep.getD 99 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ p (transLenTr ⟨99, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_99 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_99_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_99_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_99_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_99_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_99_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_99_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_99_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_99_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_99_20 hp j hj hq
  simp at hm

theorem pair_123_100 (p : Nat) (hp : p < (Q2.transData.getD 100 []).length)
    (hrep : (Q2.cosetIsRep.getD 100 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ p (transLenTr ⟨100, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_100 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_100_100 hp j hj hq
  simp at hm

theorem pair_123_108 (p : Nat) (hp : p < (Q2.transData.getD 108 []).length)
    (hrep : (Q2.cosetIsRep.getD 108 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ p (transLenTr ⟨108, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_108 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_108_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_108_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_108_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_108_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_108_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_108_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_108_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_108_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_108_20 hp j hj hq
  simp at hm

theorem pair_123_112 (p : Nat) (hp : p < (Q2.transData.getD 112 []).length)
    (hrep : (Q2.cosetIsRep.getD 112 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ p (transLenTr ⟨112, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_112 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_112_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_112_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_112_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_112_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_112_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_112_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_112_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_112_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_112_20 hp j hj hq
  simp at hm

theorem pair_123_123 (p : Nat) (hp : p < (Q2.transData.getD 123 []).length)
    (hrep : (Q2.cosetIsRep.getD 123 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 123 []).length)
    (hq : (normIsRep.getD 123 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ p hp)
        (rowE2 (⟨123, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ p (transLenTr ⟨123, by decide⟩ p hp))
        (rowE1 (⟨123, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_123 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_123_123_24 hp j hj hq
  simp at hm

theorem pair_124_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_2_4 hp j hj hq
  simp at hm

theorem pair_124_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_10_4 hp j hj hq
  simp at hm

theorem pair_124_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_12_4 hp j hj hq
  simp at hm

theorem pair_124_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_20_20 hp j hj hq
  simp at hm

theorem pair_124_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_30_20 hp j hj hq
  simp at hm

theorem pair_124_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_33_20 hp j hj hq
  simp at hm

theorem pair_124_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_39_20 hp j hj hq
  simp at hm

theorem pair_124_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_47_20 hp j hj hq
  simp at hm

theorem pair_124_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_51_20 hp j hj hq
  simp at hm

theorem pair_124_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_53_20 hp j hj hq
  simp at hm

theorem pair_124_81 (p : Nat) (hp : p < (Q2.transData.getD 81 []).length)
    (hrep : (Q2.cosetIsRep.getD 81 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ p (transLenTr ⟨81, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_81 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_81_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_81_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_81_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_81_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_81_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_81_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_81_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_81_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_81_20 hp j hj hq
  simp at hm

theorem pair_124_92 (p : Nat) (hp : p < (Q2.transData.getD 92 []).length)
    (hrep : (Q2.cosetIsRep.getD 92 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ p (transLenTr ⟨92, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_92 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_92_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_92_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_92_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_92_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_92_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_92_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_92_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_92_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_92_20 hp j hj hq
  simp at hm

theorem pair_124_95 (p : Nat) (hp : p < (Q2.transData.getD 95 []).length)
    (hrep : (Q2.cosetIsRep.getD 95 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ p (transLenTr ⟨95, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_95 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_95_100 hp j hj hq
  simp at hm

theorem pair_124_101 (p : Nat) (hp : p < (Q2.transData.getD 101 []).length)
    (hrep : (Q2.cosetIsRep.getD 101 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ p (transLenTr ⟨101, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_101 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_101_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_101_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_101_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_101_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_101_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_101_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_101_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_101_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_101_20 hp j hj hq
  simp at hm

theorem pair_124_109 (p : Nat) (hp : p < (Q2.transData.getD 109 []).length)
    (hrep : (Q2.cosetIsRep.getD 109 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ p (transLenTr ⟨109, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_109 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_109_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_109_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_109_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_109_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_109_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_109_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_109_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_109_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_109_20 hp j hj hq
  simp at hm

theorem pair_124_113 (p : Nat) (hp : p < (Q2.transData.getD 113 []).length)
    (hrep : (Q2.cosetIsRep.getD 113 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ p (transLenTr ⟨113, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_113 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_113_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_113_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_113_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_113_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_113_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_113_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_113_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_113_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_113_20 hp j hj hq
  simp at hm

theorem pair_124_124 (p : Nat) (hp : p < (Q2.transData.getD 124 []).length)
    (hrep : (Q2.cosetIsRep.getD 124 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ p hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ p (transLenTr ⟨124, by decide⟩ p hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_124 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_124_124_24 hp j hj hq
  simp at hm

theorem pair_125_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_2_4 hp j hj hq
  simp at hm

theorem pair_125_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_10_4 hp j hj hq
  simp at hm

theorem pair_125_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_12_4 hp j hj hq
  simp at hm

theorem pair_125_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_20_20 hp j hj hq
  simp at hm

theorem pair_125_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_31_20 hp j hj hq
  simp at hm

theorem pair_125_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_34_20 hp j hj hq
  simp at hm

theorem pair_125_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_40_20 hp j hj hq
  simp at hm

theorem pair_125_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_43_20 hp j hj hq
  simp at hm

theorem pair_125_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_52_20 hp j hj hq
  simp at hm

theorem pair_125_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_125_53_20 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
