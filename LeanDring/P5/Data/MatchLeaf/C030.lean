/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C008
import LeanDring.P5.Data.ColRestCheap.C044
import LeanDring.P5.Data.ColRestCheap.C045
import LeanDring.P5.Data.ColRestCheap.C046
import LeanDring.P5.Data.ColRestCheap.C047
import LeanDring.P5.Data.ColRestCheap.C048
import LeanDring.P5.Data.EntryK.C029
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C062
import LeanDring.P5.Data.SpeciesDiv.C063

/-! # Stage-5 leaves, chunk 29 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_120_79_12 (hp : 12 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 12 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 12 (transLenTr ⟨79, by decide⟩ 12 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 12 (transLenTr ⟨79, by decide⟩ 12 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 12 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_12.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_13 (hp : 13 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 13 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 13 (transLenTr ⟨79, by decide⟩ 13 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 13 (transLenTr ⟨79, by decide⟩ 13 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 13 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_13.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_14 (hp : 14 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 14 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 14 (transLenTr ⟨79, by decide⟩ 14 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 14 (transLenTr ⟨79, by decide⟩ 14 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 14 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_14.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_15 (hp : 15 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 15 (transLenTr ⟨79, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 15 (transLenTr ⟨79, by decide⟩ 15 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 15 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_16 (hp : 16 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 16 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 16 (transLenTr ⟨79, by decide⟩ 16 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 16 (transLenTr ⟨79, by decide⟩ 16 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 16 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_16.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_17 (hp : 17 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 17 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 17 (transLenTr ⟨79, by decide⟩ 17 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 17 (transLenTr ⟨79, by decide⟩ 17 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 17 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_17.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_18 (hp : 18 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 18 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 18 (transLenTr ⟨79, by decide⟩ 18 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 18 (transLenTr ⟨79, by decide⟩ 18 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 18 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_18.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_19 (hp : 19 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 19 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 19 (transLenTr ⟨79, by decide⟩ 19 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 19 (transLenTr ⟨79, by decide⟩ 19 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 19 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_19.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_20 (hp : 20 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 20 (transLenTr ⟨79, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 20 (transLenTr ⟨79, by decide⟩ 20 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 20 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_21 (hp : 21 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 21 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 21 (transLenTr ⟨79, by decide⟩ 21 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 21 (transLenTr ⟨79, by decide⟩ 21 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 21 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_21.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_22 (hp : 22 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 22 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 22 (transLenTr ⟨79, by decide⟩ 22 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 22 (transLenTr ⟨79, by decide⟩ 22 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 22 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_22.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_23 (hp : 23 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 23 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 23 (transLenTr ⟨79, by decide⟩ 23 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 23 (transLenTr ⟨79, by decide⟩ 23 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 23 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_23.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_79_24 (hp : 24 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 24 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 24 (transLenTr ⟨79, by decide⟩ 24 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 24 (transLenTr ⟨79, by decide⟩ 24 hp)) T120_79
      hfix120_79 hinj120_79 hcardT120_79
      (fun i => conj_mem_of_fixedPoints _ _ (T120_79 i) (hfix120_79 i) _)
      ⟨120, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 24 hp) Q2.T120_79_2 Q2.hfix120_79_2 Q2.hinj120_79_2
      Q2.hcardT120_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_79_2 i) (Q2.hfix120_79_2 i) _)
      colCert_120_79_24.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_0 (hp : 0 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 0 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_1 (hp : 1 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 1 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_2 (hp : 2 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 2 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_3 (hp : 3 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 3 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_4 (hp : 4 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 4 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_5 (hp : 5 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 5 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_10 (hp : 10 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 10 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_15 (hp : 15 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 15 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_20 (hp : 20 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 20 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_25 (hp : 25 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 25 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 25 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_25.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_30 (hp : 30 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 30 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 30 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_30.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_35 (hp : 35 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 35 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 35 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_35.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_40 (hp : 40 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 40 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 40 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_40.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_45 (hp : 45 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 45 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 45 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_45.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_50 (hp : 50 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 50 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 50 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_50.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_55 (hp : 55 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 55 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 55 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_55.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_60 (hp : 60 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 60 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 60 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_60.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_65 (hp : 65 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 65 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 65 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_65.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_70 (hp : 70 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 70 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 70 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_70.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_75 (hp : 75 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 75 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 75 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_75.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_80 (hp : 80 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 80 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 80 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_80.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_85 (hp : 85 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 85 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 85 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_85.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_90 (hp : 90 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 90 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 90 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_90.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_95 (hp : 95 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 95 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 95 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_95.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_100 (hp : 100 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 100 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 100 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_100.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_105 (hp : 105 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 105 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 105 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_105.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_110 (hp : 110 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 110 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 110 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_110.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_115 (hp : 115 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 115 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 115 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_115.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_80_120 (hp : 120 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 120 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp)) T120_80
      hfix120_80 hinj120_80 hcardT120_80
      (fun i => conj_mem_of_fixedPoints _ _ (T120_80 i) (hfix120_80 i) _)
      ⟨120, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 120 hp) Q2.T120_80_2 Q2.hfix120_80_2 Q2.hinj120_80_2
      Q2.hcardT120_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_80_2 i) (Q2.hfix120_80_2 i) _)
      colCert_120_80_120.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_94_0 (hp : 0 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp)) T120_94
      hfix120_94 hinj120_94 hcardT120_94
      (fun i => conj_mem_of_fixedPoints _ _ (T120_94 i) (hfix120_94 i) _)
      ⟨120, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 0 hp) Q2.T120_94_2 Q2.hfix120_94_2 Q2.hinj120_94_2
      Q2.hcardT120_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_94_2 i) (Q2.hfix120_94_2 i) _)
      colCert_120_94_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_94_1 (hp : 1 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp)) T120_94
      hfix120_94 hinj120_94 hcardT120_94
      (fun i => conj_mem_of_fixedPoints _ _ (T120_94 i) (hfix120_94 i) _)
      ⟨120, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 1 hp) Q2.T120_94_2 Q2.hfix120_94_2 Q2.hinj120_94_2
      Q2.hcardT120_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_94_2 i) (Q2.hfix120_94_2 i) _)
      colCert_120_94_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_94_2 (hp : 2 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp)) T120_94
      hfix120_94 hinj120_94 hcardT120_94
      (fun i => conj_mem_of_fixedPoints _ _ (T120_94 i) (hfix120_94 i) _)
      ⟨120, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 2 hp) Q2.T120_94_2 Q2.hfix120_94_2 Q2.hinj120_94_2
      Q2.hcardT120_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_94_2 i) (Q2.hfix120_94_2 i) _)
      colCert_120_94_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_94_3 (hp : 3 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp)) T120_94
      hfix120_94 hinj120_94 hcardT120_94
      (fun i => conj_mem_of_fixedPoints _ _ (T120_94 i) (hfix120_94 i) _)
      ⟨120, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 3 hp) Q2.T120_94_2 Q2.hfix120_94_2 Q2.hinj120_94_2
      Q2.hcardT120_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_94_2 i) (Q2.hfix120_94_2 i) _)
      colCert_120_94_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_94_4 (hp : 4 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp)) T120_94
      hfix120_94 hinj120_94 hcardT120_94
      (fun i => conj_mem_of_fixedPoints _ _ (T120_94 i) (hfix120_94 i) _)
      ⟨120, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 4 hp) Q2.T120_94_2 Q2.hfix120_94_2 Q2.hinj120_94_2
      Q2.hcardT120_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_94_2 i) (Q2.hfix120_94_2 i) _)
      colCert_120_94_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_94_5 (hp : 5 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp)) T120_94
      hfix120_94 hinj120_94 hcardT120_94
      (fun i => conj_mem_of_fixedPoints _ _ (T120_94 i) (hfix120_94 i) _)
      ⟨120, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 5 hp) Q2.T120_94_2 Q2.hfix120_94_2 Q2.hinj120_94_2
      Q2.hcardT120_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_94_2 i) (Q2.hfix120_94_2 i) _)
      colCert_120_94_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_94_10 (hp : 10 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp)) T120_94
      hfix120_94 hinj120_94 hcardT120_94
      (fun i => conj_mem_of_fixedPoints _ _ (T120_94 i) (hfix120_94 i) _)
      ⟨120, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 10 hp) Q2.T120_94_2 Q2.hfix120_94_2 Q2.hinj120_94_2
      Q2.hcardT120_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_94_2 i) (Q2.hfix120_94_2 i) _)
      colCert_120_94_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_94_15 (hp : 15 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp)) T120_94
      hfix120_94 hinj120_94 hcardT120_94
      (fun i => conj_mem_of_fixedPoints _ _ (T120_94 i) (hfix120_94 i) _)
      ⟨120, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 15 hp) Q2.T120_94_2 Q2.hfix120_94_2 Q2.hinj120_94_2
      Q2.hcardT120_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_94_2 i) (Q2.hfix120_94_2 i) _)
      colCert_120_94_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_94_20 (hp : 20 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp)) T120_94
      hfix120_94 hinj120_94 hcardT120_94
      (fun i => conj_mem_of_fixedPoints _ _ (T120_94 i) (hfix120_94 i) _)
      ⟨120, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 20 hp) Q2.T120_94_2 Q2.hfix120_94_2 Q2.hinj120_94_2
      Q2.hcardT120_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_94_2 i) (Q2.hfix120_94_2 i) _)
      colCert_120_94_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_99_0 (hp : 0 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp)) T120_99
      hfix120_99 hinj120_99 hcardT120_99
      (fun i => conj_mem_of_fixedPoints _ _ (T120_99 i) (hfix120_99 i) _)
      ⟨120, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 0 hp) Q2.T120_99_2 Q2.hfix120_99_2 Q2.hinj120_99_2
      Q2.hcardT120_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_99_2 i) (Q2.hfix120_99_2 i) _)
      colCert_120_99_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_99_1 (hp : 1 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp)) T120_99
      hfix120_99 hinj120_99 hcardT120_99
      (fun i => conj_mem_of_fixedPoints _ _ (T120_99 i) (hfix120_99 i) _)
      ⟨120, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 1 hp) Q2.T120_99_2 Q2.hfix120_99_2 Q2.hinj120_99_2
      Q2.hcardT120_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_99_2 i) (Q2.hfix120_99_2 i) _)
      colCert_120_99_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_99_2 (hp : 2 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp)) T120_99
      hfix120_99 hinj120_99 hcardT120_99
      (fun i => conj_mem_of_fixedPoints _ _ (T120_99 i) (hfix120_99 i) _)
      ⟨120, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 2 hp) Q2.T120_99_2 Q2.hfix120_99_2 Q2.hinj120_99_2
      Q2.hcardT120_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_99_2 i) (Q2.hfix120_99_2 i) _)
      colCert_120_99_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_99_3 (hp : 3 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp)) T120_99
      hfix120_99 hinj120_99 hcardT120_99
      (fun i => conj_mem_of_fixedPoints _ _ (T120_99 i) (hfix120_99 i) _)
      ⟨120, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 3 hp) Q2.T120_99_2 Q2.hfix120_99_2 Q2.hinj120_99_2
      Q2.hcardT120_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_99_2 i) (Q2.hfix120_99_2 i) _)
      colCert_120_99_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_99_4 (hp : 4 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp)) T120_99
      hfix120_99 hinj120_99 hcardT120_99
      (fun i => conj_mem_of_fixedPoints _ _ (T120_99 i) (hfix120_99 i) _)
      ⟨120, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 4 hp) Q2.T120_99_2 Q2.hfix120_99_2 Q2.hinj120_99_2
      Q2.hcardT120_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_99_2 i) (Q2.hfix120_99_2 i) _)
      colCert_120_99_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_99_5 (hp : 5 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp)) T120_99
      hfix120_99 hinj120_99 hcardT120_99
      (fun i => conj_mem_of_fixedPoints _ _ (T120_99 i) (hfix120_99 i) _)
      ⟨120, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 5 hp) Q2.T120_99_2 Q2.hfix120_99_2 Q2.hinj120_99_2
      Q2.hcardT120_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_99_2 i) (Q2.hfix120_99_2 i) _)
      colCert_120_99_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_99_10 (hp : 10 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp)) T120_99
      hfix120_99 hinj120_99 hcardT120_99
      (fun i => conj_mem_of_fixedPoints _ _ (T120_99 i) (hfix120_99 i) _)
      ⟨120, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 10 hp) Q2.T120_99_2 Q2.hfix120_99_2 Q2.hinj120_99_2
      Q2.hcardT120_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_99_2 i) (Q2.hfix120_99_2 i) _)
      colCert_120_99_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_99_15 (hp : 15 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp)) T120_99
      hfix120_99 hinj120_99 hcardT120_99
      (fun i => conj_mem_of_fixedPoints _ _ (T120_99 i) (hfix120_99 i) _)
      ⟨120, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 15 hp) Q2.T120_99_2 Q2.hfix120_99_2 Q2.hinj120_99_2
      Q2.hcardT120_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_99_2 i) (Q2.hfix120_99_2 i) _)
      colCert_120_99_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_99_20 (hp : 20 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp)) T120_99
      hfix120_99 hinj120_99 hcardT120_99
      (fun i => conj_mem_of_fixedPoints _ _ (T120_99 i) (hfix120_99 i) _)
      ⟨120, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 20 hp) Q2.T120_99_2 Q2.hfix120_99_2 Q2.hinj120_99_2
      Q2.hcardT120_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_99_2 i) (Q2.hfix120_99_2 i) _)
      colCert_120_99_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_104_0 (hp : 0 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp)) T120_104
      hfix120_104 hinj120_104 hcardT120_104
      (fun i => conj_mem_of_fixedPoints _ _ (T120_104 i) (hfix120_104 i) _)
      ⟨120, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 0 hp) Q2.T120_104_2 Q2.hfix120_104_2 Q2.hinj120_104_2
      Q2.hcardT120_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_104_2 i) (Q2.hfix120_104_2 i) _)
      colCert_120_104_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_104_1 (hp : 1 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp)) T120_104
      hfix120_104 hinj120_104 hcardT120_104
      (fun i => conj_mem_of_fixedPoints _ _ (T120_104 i) (hfix120_104 i) _)
      ⟨120, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 1 hp) Q2.T120_104_2 Q2.hfix120_104_2 Q2.hinj120_104_2
      Q2.hcardT120_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_104_2 i) (Q2.hfix120_104_2 i) _)
      colCert_120_104_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_104_2 (hp : 2 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp)) T120_104
      hfix120_104 hinj120_104 hcardT120_104
      (fun i => conj_mem_of_fixedPoints _ _ (T120_104 i) (hfix120_104 i) _)
      ⟨120, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 2 hp) Q2.T120_104_2 Q2.hfix120_104_2 Q2.hinj120_104_2
      Q2.hcardT120_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_104_2 i) (Q2.hfix120_104_2 i) _)
      colCert_120_104_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_104_3 (hp : 3 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp)) T120_104
      hfix120_104 hinj120_104 hcardT120_104
      (fun i => conj_mem_of_fixedPoints _ _ (T120_104 i) (hfix120_104 i) _)
      ⟨120, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 3 hp) Q2.T120_104_2 Q2.hfix120_104_2 Q2.hinj120_104_2
      Q2.hcardT120_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_104_2 i) (Q2.hfix120_104_2 i) _)
      colCert_120_104_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_104_4 (hp : 4 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp)) T120_104
      hfix120_104 hinj120_104 hcardT120_104
      (fun i => conj_mem_of_fixedPoints _ _ (T120_104 i) (hfix120_104 i) _)
      ⟨120, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 4 hp) Q2.T120_104_2 Q2.hfix120_104_2 Q2.hinj120_104_2
      Q2.hcardT120_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_104_2 i) (Q2.hfix120_104_2 i) _)
      colCert_120_104_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_104_5 (hp : 5 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp)) T120_104
      hfix120_104 hinj120_104 hcardT120_104
      (fun i => conj_mem_of_fixedPoints _ _ (T120_104 i) (hfix120_104 i) _)
      ⟨120, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 5 hp) Q2.T120_104_2 Q2.hfix120_104_2 Q2.hinj120_104_2
      Q2.hcardT120_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_104_2 i) (Q2.hfix120_104_2 i) _)
      colCert_120_104_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_104_10 (hp : 10 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp)) T120_104
      hfix120_104 hinj120_104 hcardT120_104
      (fun i => conj_mem_of_fixedPoints _ _ (T120_104 i) (hfix120_104 i) _)
      ⟨120, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 10 hp) Q2.T120_104_2 Q2.hfix120_104_2 Q2.hinj120_104_2
      Q2.hcardT120_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_104_2 i) (Q2.hfix120_104_2 i) _)
      colCert_120_104_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_104_15 (hp : 15 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp)) T120_104
      hfix120_104 hinj120_104 hcardT120_104
      (fun i => conj_mem_of_fixedPoints _ _ (T120_104 i) (hfix120_104 i) _)
      ⟨120, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 15 hp) Q2.T120_104_2 Q2.hfix120_104_2 Q2.hinj120_104_2
      Q2.hcardT120_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_104_2 i) (Q2.hfix120_104_2 i) _)
      colCert_120_104_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_104_20 (hp : 20 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp)) T120_104
      hfix120_104 hinj120_104 hcardT120_104
      (fun i => conj_mem_of_fixedPoints _ _ (T120_104 i) (hfix120_104 i) _)
      ⟨120, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 20 hp) Q2.T120_104_2 Q2.hfix120_104_2 Q2.hinj120_104_2
      Q2.hcardT120_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_104_2 i) (Q2.hfix120_104_2 i) _)
      colCert_120_104_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_109_0 (hp : 0 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp)) T120_109
      hfix120_109 hinj120_109 hcardT120_109
      (fun i => conj_mem_of_fixedPoints _ _ (T120_109 i) (hfix120_109 i) _)
      ⟨120, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 0 hp) Q2.T120_109_2 Q2.hfix120_109_2 Q2.hinj120_109_2
      Q2.hcardT120_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_109_2 i) (Q2.hfix120_109_2 i) _)
      colCert_120_109_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_109_1 (hp : 1 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp)) T120_109
      hfix120_109 hinj120_109 hcardT120_109
      (fun i => conj_mem_of_fixedPoints _ _ (T120_109 i) (hfix120_109 i) _)
      ⟨120, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 1 hp) Q2.T120_109_2 Q2.hfix120_109_2 Q2.hinj120_109_2
      Q2.hcardT120_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_109_2 i) (Q2.hfix120_109_2 i) _)
      colCert_120_109_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_109_2 (hp : 2 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp)) T120_109
      hfix120_109 hinj120_109 hcardT120_109
      (fun i => conj_mem_of_fixedPoints _ _ (T120_109 i) (hfix120_109 i) _)
      ⟨120, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 2 hp) Q2.T120_109_2 Q2.hfix120_109_2 Q2.hinj120_109_2
      Q2.hcardT120_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_109_2 i) (Q2.hfix120_109_2 i) _)
      colCert_120_109_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_109_3 (hp : 3 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp)) T120_109
      hfix120_109 hinj120_109 hcardT120_109
      (fun i => conj_mem_of_fixedPoints _ _ (T120_109 i) (hfix120_109 i) _)
      ⟨120, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 3 hp) Q2.T120_109_2 Q2.hfix120_109_2 Q2.hinj120_109_2
      Q2.hcardT120_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_109_2 i) (Q2.hfix120_109_2 i) _)
      colCert_120_109_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_109_4 (hp : 4 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp)) T120_109
      hfix120_109 hinj120_109 hcardT120_109
      (fun i => conj_mem_of_fixedPoints _ _ (T120_109 i) (hfix120_109 i) _)
      ⟨120, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 4 hp) Q2.T120_109_2 Q2.hfix120_109_2 Q2.hinj120_109_2
      Q2.hcardT120_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_109_2 i) (Q2.hfix120_109_2 i) _)
      colCert_120_109_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_109_5 (hp : 5 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp)) T120_109
      hfix120_109 hinj120_109 hcardT120_109
      (fun i => conj_mem_of_fixedPoints _ _ (T120_109 i) (hfix120_109 i) _)
      ⟨120, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 5 hp) Q2.T120_109_2 Q2.hfix120_109_2 Q2.hinj120_109_2
      Q2.hcardT120_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_109_2 i) (Q2.hfix120_109_2 i) _)
      colCert_120_109_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_109_10 (hp : 10 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp)) T120_109
      hfix120_109 hinj120_109 hcardT120_109
      (fun i => conj_mem_of_fixedPoints _ _ (T120_109 i) (hfix120_109 i) _)
      ⟨120, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 10 hp) Q2.T120_109_2 Q2.hfix120_109_2 Q2.hinj120_109_2
      Q2.hcardT120_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_109_2 i) (Q2.hfix120_109_2 i) _)
      colCert_120_109_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_109_15 (hp : 15 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp)) T120_109
      hfix120_109 hinj120_109 hcardT120_109
      (fun i => conj_mem_of_fixedPoints _ _ (T120_109 i) (hfix120_109 i) _)
      ⟨120, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 15 hp) Q2.T120_109_2 Q2.hfix120_109_2 Q2.hinj120_109_2
      Q2.hcardT120_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_109_2 i) (Q2.hfix120_109_2 i) _)
      colCert_120_109_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_109_20 (hp : 20 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp)) T120_109
      hfix120_109 hinj120_109 hcardT120_109
      (fun i => conj_mem_of_fixedPoints _ _ (T120_109 i) (hfix120_109 i) _)
      ⟨120, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 20 hp) Q2.T120_109_2 Q2.hfix120_109_2 Q2.hinj120_109_2
      Q2.hcardT120_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_109_2 i) (Q2.hfix120_109_2 i) _)
      colCert_120_109_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_114_0 (hp : 0 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp)) T120_114
      hfix120_114 hinj120_114 hcardT120_114
      (fun i => conj_mem_of_fixedPoints _ _ (T120_114 i) (hfix120_114 i) _)
      ⟨120, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 0 hp) Q2.T120_114_2 Q2.hfix120_114_2 Q2.hinj120_114_2
      Q2.hcardT120_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_114_2 i) (Q2.hfix120_114_2 i) _)
      colCert_120_114_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_114_1 (hp : 1 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp)) T120_114
      hfix120_114 hinj120_114 hcardT120_114
      (fun i => conj_mem_of_fixedPoints _ _ (T120_114 i) (hfix120_114 i) _)
      ⟨120, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 1 hp) Q2.T120_114_2 Q2.hfix120_114_2 Q2.hinj120_114_2
      Q2.hcardT120_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_114_2 i) (Q2.hfix120_114_2 i) _)
      colCert_120_114_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_114_2 (hp : 2 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp)) T120_114
      hfix120_114 hinj120_114 hcardT120_114
      (fun i => conj_mem_of_fixedPoints _ _ (T120_114 i) (hfix120_114 i) _)
      ⟨120, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 2 hp) Q2.T120_114_2 Q2.hfix120_114_2 Q2.hinj120_114_2
      Q2.hcardT120_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_114_2 i) (Q2.hfix120_114_2 i) _)
      colCert_120_114_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_114_3 (hp : 3 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp)) T120_114
      hfix120_114 hinj120_114 hcardT120_114
      (fun i => conj_mem_of_fixedPoints _ _ (T120_114 i) (hfix120_114 i) _)
      ⟨120, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 3 hp) Q2.T120_114_2 Q2.hfix120_114_2 Q2.hinj120_114_2
      Q2.hcardT120_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_114_2 i) (Q2.hfix120_114_2 i) _)
      colCert_120_114_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_114_4 (hp : 4 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp)) T120_114
      hfix120_114 hinj120_114 hcardT120_114
      (fun i => conj_mem_of_fixedPoints _ _ (T120_114 i) (hfix120_114 i) _)
      ⟨120, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 4 hp) Q2.T120_114_2 Q2.hfix120_114_2 Q2.hinj120_114_2
      Q2.hcardT120_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_114_2 i) (Q2.hfix120_114_2 i) _)
      colCert_120_114_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_114_5 (hp : 5 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp)) T120_114
      hfix120_114 hinj120_114 hcardT120_114
      (fun i => conj_mem_of_fixedPoints _ _ (T120_114 i) (hfix120_114 i) _)
      ⟨120, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 5 hp) Q2.T120_114_2 Q2.hfix120_114_2 Q2.hinj120_114_2
      Q2.hcardT120_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_114_2 i) (Q2.hfix120_114_2 i) _)
      colCert_120_114_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_114_10 (hp : 10 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp)) T120_114
      hfix120_114 hinj120_114 hcardT120_114
      (fun i => conj_mem_of_fixedPoints _ _ (T120_114 i) (hfix120_114 i) _)
      ⟨120, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 10 hp) Q2.T120_114_2 Q2.hfix120_114_2 Q2.hinj120_114_2
      Q2.hcardT120_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_114_2 i) (Q2.hfix120_114_2 i) _)
      colCert_120_114_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_114_15 (hp : 15 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp)) T120_114
      hfix120_114 hinj120_114 hcardT120_114
      (fun i => conj_mem_of_fixedPoints _ _ (T120_114 i) (hfix120_114 i) _)
      ⟨120, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 15 hp) Q2.T120_114_2 Q2.hfix120_114_2 Q2.hinj120_114_2
      Q2.hcardT120_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_114_2 i) (Q2.hfix120_114_2 i) _)
      colCert_120_114_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_114_20 (hp : 20 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp)) T120_114
      hfix120_114 hinj120_114 hcardT120_114
      (fun i => conj_mem_of_fixedPoints _ _ (T120_114 i) (hfix120_114 i) _)
      ⟨120, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 20 hp) Q2.T120_114_2 Q2.hfix120_114_2 Q2.hinj120_114_2
      Q2.hcardT120_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_114_2 i) (Q2.hfix120_114_2 i) _)
      colCert_120_114_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_0 (hp : 0 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 0 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 0 (transLenTr ⟨120, by decide⟩ 0 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 0 (transLenTr ⟨120, by decide⟩ 0 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 0 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_0.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_1 (hp : 1 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 1 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 1 (transLenTr ⟨120, by decide⟩ 1 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 1 (transLenTr ⟨120, by decide⟩ 1 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 1 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_1.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_2 (hp : 2 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 2 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 2 (transLenTr ⟨120, by decide⟩ 2 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 2 (transLenTr ⟨120, by decide⟩ 2 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 2 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_2.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_3 (hp : 3 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 3 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 3 (transLenTr ⟨120, by decide⟩ 3 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 3 (transLenTr ⟨120, by decide⟩ 3 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 3 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_3.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_4 (hp : 4 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 4 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 4 (transLenTr ⟨120, by decide⟩ 4 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 4 (transLenTr ⟨120, by decide⟩ 4 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 4 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_4.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_5 (hp : 5 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 5 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 5 (transLenTr ⟨120, by decide⟩ 5 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 5 (transLenTr ⟨120, by decide⟩ 5 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 5 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_5.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_6 (hp : 6 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 6 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 6 (transLenTr ⟨120, by decide⟩ 6 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 6 (transLenTr ⟨120, by decide⟩ 6 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 6 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_6.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_7 (hp : 7 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 7 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 7 (transLenTr ⟨120, by decide⟩ 7 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 7 (transLenTr ⟨120, by decide⟩ 7 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 7 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_7.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_8 (hp : 8 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 8 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 8 (transLenTr ⟨120, by decide⟩ 8 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 8 (transLenTr ⟨120, by decide⟩ 8 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 8 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_8.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_9 (hp : 9 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 9 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 9 (transLenTr ⟨120, by decide⟩ 9 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 9 (transLenTr ⟨120, by decide⟩ 9 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 9 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_9.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_10 (hp : 10 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 10 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 10 (transLenTr ⟨120, by decide⟩ 10 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 10 (transLenTr ⟨120, by decide⟩ 10 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 10 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_10.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_11 (hp : 11 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 11 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 11 (transLenTr ⟨120, by decide⟩ 11 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 11 (transLenTr ⟨120, by decide⟩ 11 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 11 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_11.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_12 (hp : 12 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 12 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 12 (transLenTr ⟨120, by decide⟩ 12 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 12 (transLenTr ⟨120, by decide⟩ 12 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 12 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_12.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_13 (hp : 13 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 13 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 13 (transLenTr ⟨120, by decide⟩ 13 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 13 (transLenTr ⟨120, by decide⟩ 13 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 13 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_13.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_14 (hp : 14 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 14 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 14 (transLenTr ⟨120, by decide⟩ 14 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 14 (transLenTr ⟨120, by decide⟩ 14 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 14 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_14.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_15 (hp : 15 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 15 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 15 (transLenTr ⟨120, by decide⟩ 15 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 15 (transLenTr ⟨120, by decide⟩ 15 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 15 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_15.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_16 (hp : 16 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 16 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 16 (transLenTr ⟨120, by decide⟩ 16 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 16 (transLenTr ⟨120, by decide⟩ 16 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 16 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_16.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_17 (hp : 17 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 17 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 17 (transLenTr ⟨120, by decide⟩ 17 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 17 (transLenTr ⟨120, by decide⟩ 17 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 17 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_17.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_18 (hp : 18 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 18 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 18 (transLenTr ⟨120, by decide⟩ 18 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 18 (transLenTr ⟨120, by decide⟩ 18 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 18 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_18.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_19 (hp : 19 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 19 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 19 (transLenTr ⟨120, by decide⟩ 19 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 19 (transLenTr ⟨120, by decide⟩ 19 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 19 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_19.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_20 (hp : 20 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 20 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 20 (transLenTr ⟨120, by decide⟩ 20 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 20 (transLenTr ⟨120, by decide⟩ 20 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 20 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_20.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_21 (hp : 21 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 21 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 21 (transLenTr ⟨120, by decide⟩ 21 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 21 (transLenTr ⟨120, by decide⟩ 21 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 21 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_21.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_22 (hp : 22 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 22 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 22 (transLenTr ⟨120, by decide⟩ 22 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 22 (transLenTr ⟨120, by decide⟩ 22 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 22 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_22.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_23 (hp : 23 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 23 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 23 (transLenTr ⟨120, by decide⟩ 23 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 23 (transLenTr ⟨120, by decide⟩ 23 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 23 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_23.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_24 (hp : 24 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 24 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 24 (transLenTr ⟨120, by decide⟩ 24 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 24 (transLenTr ⟨120, by decide⟩ 24 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 24 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_24.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_25 (hp : 25 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 25 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 25 (transLenTr ⟨120, by decide⟩ 25 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 25 (transLenTr ⟨120, by decide⟩ 25 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 25 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_25.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_30 (hp : 30 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 30 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 30 (transLenTr ⟨120, by decide⟩ 30 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 30 (transLenTr ⟨120, by decide⟩ 30 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 30 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_30.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_35 (hp : 35 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 35 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 35 (transLenTr ⟨120, by decide⟩ 35 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 35 (transLenTr ⟨120, by decide⟩ 35 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 35 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_35.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_40 (hp : 40 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 40 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 40 (transLenTr ⟨120, by decide⟩ 40 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 40 (transLenTr ⟨120, by decide⟩ 40 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 40 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_40.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_45 (hp : 45 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 45 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 45 (transLenTr ⟨120, by decide⟩ 45 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 45 (transLenTr ⟨120, by decide⟩ 45 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 45 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_45.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_50 (hp : 50 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 50 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 50 (transLenTr ⟨120, by decide⟩ 50 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 50 (transLenTr ⟨120, by decide⟩ 50 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 50 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_50.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_55 (hp : 55 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 55 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 55 (transLenTr ⟨120, by decide⟩ 55 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 55 (transLenTr ⟨120, by decide⟩ 55 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 55 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_55.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_60 (hp : 60 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 60 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 60 (transLenTr ⟨120, by decide⟩ 60 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 60 (transLenTr ⟨120, by decide⟩ 60 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 60 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_60.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_65 (hp : 65 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 65 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 65 (transLenTr ⟨120, by decide⟩ 65 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 65 (transLenTr ⟨120, by decide⟩ 65 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 65 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_65.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_70 (hp : 70 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 70 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 70 (transLenTr ⟨120, by decide⟩ 70 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 70 (transLenTr ⟨120, by decide⟩ 70 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 70 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_70.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_75 (hp : 75 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 75 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 75 (transLenTr ⟨120, by decide⟩ 75 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 75 (transLenTr ⟨120, by decide⟩ 75 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 75 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_75.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_80 (hp : 80 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 80 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 80 (transLenTr ⟨120, by decide⟩ 80 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 80 (transLenTr ⟨120, by decide⟩ 80 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 80 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_80.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_85 (hp : 85 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 85 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 85 (transLenTr ⟨120, by decide⟩ 85 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 85 (transLenTr ⟨120, by decide⟩ 85 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 85 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_85.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_90 (hp : 90 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 90 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 90 (transLenTr ⟨120, by decide⟩ 90 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 90 (transLenTr ⟨120, by decide⟩ 90 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 90 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_90.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_95 (hp : 95 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 95 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 95 (transLenTr ⟨120, by decide⟩ 95 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 95 (transLenTr ⟨120, by decide⟩ 95 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 95 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_95.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_100 (hp : 100 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 100 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 100 (transLenTr ⟨120, by decide⟩ 100 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 100 (transLenTr ⟨120, by decide⟩ 100 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 100 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_100.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_105 (hp : 105 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 105 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 105 (transLenTr ⟨120, by decide⟩ 105 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 105 (transLenTr ⟨120, by decide⟩ 105 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 105 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_105.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_110 (hp : 110 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 110 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 110 (transLenTr ⟨120, by decide⟩ 110 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 110 (transLenTr ⟨120, by decide⟩ 110 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 110 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_110.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_115 (hp : 115 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 115 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 115 (transLenTr ⟨120, by decide⟩ 115 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 115 (transLenTr ⟨120, by decide⟩ 115 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 115 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_115.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_120_120_120 (hp : 120 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 120 []).length)
    (hq : (normIsRep.getD 120 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 120 hp)
        (rowE2 (⟨120, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 120 (transLenTr ⟨120, by decide⟩ 120 hp))
        (rowE1 (⟨120, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨120, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨120, by decide⟩ (listedAt ⟨120, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 120 (transLenTr ⟨120, by decide⟩ 120 hp)) T120_120
      hfix120_120 hinj120_120 hcardT120_120
      (fun i => conj_mem_of_fixedPoints _ _ (T120_120 i) (hfix120_120 i) _)
      ⟨120, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨120, by decide⟩ (Q2.listedAt ⟨120, by decide⟩
        (alnCheck_rep ⟨120, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 120 hp) Q2.T120_120_2 Q2.hfix120_120_2 Q2.hinj120_120_2
      Q2.hcardT120_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T120_120_2 i) (Q2.hfix120_120_2 i) _)
      colCert_120_120_120.hD ?_).symm
  rw [alnId_120 j hj]


theorem leaf_121_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T121_2
      hfix121_2 hinj121_2 hcardT121_2
      (fun i => conj_mem_of_fixedPoints _ _ (T121_2 i) (hfix121_2 i) _)
      ⟨121, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T121_2_2 Q2.hfix121_2_2 Q2.hinj121_2_2
      Q2.hcardT121_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_2_2 i) (Q2.hfix121_2_2 i) _)
      colCert_121_2_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T121_2
      hfix121_2 hinj121_2 hcardT121_2
      (fun i => conj_mem_of_fixedPoints _ _ (T121_2 i) (hfix121_2 i) _)
      ⟨121, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T121_2_2 Q2.hfix121_2_2 Q2.hinj121_2_2
      Q2.hcardT121_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_2_2 i) (Q2.hfix121_2_2 i) _)
      colCert_121_2_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T121_2
      hfix121_2 hinj121_2 hcardT121_2
      (fun i => conj_mem_of_fixedPoints _ _ (T121_2 i) (hfix121_2 i) _)
      ⟨121, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T121_2_2 Q2.hfix121_2_2 Q2.hinj121_2_2
      Q2.hcardT121_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_2_2 i) (Q2.hfix121_2_2 i) _)
      colCert_121_2_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T121_2
      hfix121_2 hinj121_2 hcardT121_2
      (fun i => conj_mem_of_fixedPoints _ _ (T121_2 i) (hfix121_2 i) _)
      ⟨121, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T121_2_2 Q2.hfix121_2_2 Q2.hinj121_2_2
      Q2.hcardT121_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_2_2 i) (Q2.hfix121_2_2 i) _)
      colCert_121_2_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T121_2
      hfix121_2 hinj121_2 hcardT121_2
      (fun i => conj_mem_of_fixedPoints _ _ (T121_2 i) (hfix121_2 i) _)
      ⟨121, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T121_2_2 Q2.hfix121_2_2 Q2.hinj121_2_2
      Q2.hcardT121_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_2_2 i) (Q2.hfix121_2_2 i) _)
      colCert_121_2_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T121_10
      hfix121_10 hinj121_10 hcardT121_10
      (fun i => conj_mem_of_fixedPoints _ _ (T121_10 i) (hfix121_10 i) _)
      ⟨121, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T121_10_2 Q2.hfix121_10_2 Q2.hinj121_10_2
      Q2.hcardT121_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_10_2 i) (Q2.hfix121_10_2 i) _)
      colCert_121_10_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T121_10
      hfix121_10 hinj121_10 hcardT121_10
      (fun i => conj_mem_of_fixedPoints _ _ (T121_10 i) (hfix121_10 i) _)
      ⟨121, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T121_10_2 Q2.hfix121_10_2 Q2.hinj121_10_2
      Q2.hcardT121_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_10_2 i) (Q2.hfix121_10_2 i) _)
      colCert_121_10_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T121_10
      hfix121_10 hinj121_10 hcardT121_10
      (fun i => conj_mem_of_fixedPoints _ _ (T121_10 i) (hfix121_10 i) _)
      ⟨121, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T121_10_2 Q2.hfix121_10_2 Q2.hinj121_10_2
      Q2.hcardT121_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_10_2 i) (Q2.hfix121_10_2 i) _)
      colCert_121_10_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T121_10
      hfix121_10 hinj121_10 hcardT121_10
      (fun i => conj_mem_of_fixedPoints _ _ (T121_10 i) (hfix121_10 i) _)
      ⟨121, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T121_10_2 Q2.hfix121_10_2 Q2.hinj121_10_2
      Q2.hcardT121_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_10_2 i) (Q2.hfix121_10_2 i) _)
      colCert_121_10_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T121_10
      hfix121_10 hinj121_10 hcardT121_10
      (fun i => conj_mem_of_fixedPoints _ _ (T121_10 i) (hfix121_10 i) _)
      ⟨121, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T121_10_2 Q2.hfix121_10_2 Q2.hinj121_10_2
      Q2.hcardT121_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_10_2 i) (Q2.hfix121_10_2 i) _)
      colCert_121_10_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T121_12
      hfix121_12 hinj121_12 hcardT121_12
      (fun i => conj_mem_of_fixedPoints _ _ (T121_12 i) (hfix121_12 i) _)
      ⟨121, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T121_12_2 Q2.hfix121_12_2 Q2.hinj121_12_2
      Q2.hcardT121_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_12_2 i) (Q2.hfix121_12_2 i) _)
      colCert_121_12_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T121_12
      hfix121_12 hinj121_12 hcardT121_12
      (fun i => conj_mem_of_fixedPoints _ _ (T121_12 i) (hfix121_12 i) _)
      ⟨121, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T121_12_2 Q2.hfix121_12_2 Q2.hinj121_12_2
      Q2.hcardT121_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_12_2 i) (Q2.hfix121_12_2 i) _)
      colCert_121_12_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T121_12
      hfix121_12 hinj121_12 hcardT121_12
      (fun i => conj_mem_of_fixedPoints _ _ (T121_12 i) (hfix121_12 i) _)
      ⟨121, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T121_12_2 Q2.hfix121_12_2 Q2.hinj121_12_2
      Q2.hcardT121_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_12_2 i) (Q2.hfix121_12_2 i) _)
      colCert_121_12_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T121_12
      hfix121_12 hinj121_12 hcardT121_12
      (fun i => conj_mem_of_fixedPoints _ _ (T121_12 i) (hfix121_12 i) _)
      ⟨121, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T121_12_2 Q2.hfix121_12_2 Q2.hinj121_12_2
      Q2.hcardT121_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_12_2 i) (Q2.hfix121_12_2 i) _)
      colCert_121_12_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T121_12
      hfix121_12 hinj121_12 hcardT121_12
      (fun i => conj_mem_of_fixedPoints _ _ (T121_12 i) (hfix121_12 i) _)
      ⟨121, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T121_12_2 Q2.hfix121_12_2 Q2.hinj121_12_2
      Q2.hcardT121_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_12_2 i) (Q2.hfix121_12_2 i) _)
      colCert_121_12_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T121_20
      hfix121_20 hinj121_20 hcardT121_20
      (fun i => conj_mem_of_fixedPoints _ _ (T121_20 i) (hfix121_20 i) _)
      ⟨121, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T121_20_2 Q2.hfix121_20_2 Q2.hinj121_20_2
      Q2.hcardT121_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_20_2 i) (Q2.hfix121_20_2 i) _)
      colCert_121_20_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T121_20
      hfix121_20 hinj121_20 hcardT121_20
      (fun i => conj_mem_of_fixedPoints _ _ (T121_20 i) (hfix121_20 i) _)
      ⟨121, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T121_20_2 Q2.hfix121_20_2 Q2.hinj121_20_2
      Q2.hcardT121_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_20_2 i) (Q2.hfix121_20_2 i) _)
      colCert_121_20_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T121_20
      hfix121_20 hinj121_20 hcardT121_20
      (fun i => conj_mem_of_fixedPoints _ _ (T121_20 i) (hfix121_20 i) _)
      ⟨121, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T121_20_2 Q2.hfix121_20_2 Q2.hinj121_20_2
      Q2.hcardT121_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_20_2 i) (Q2.hfix121_20_2 i) _)
      colCert_121_20_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T121_20
      hfix121_20 hinj121_20 hcardT121_20
      (fun i => conj_mem_of_fixedPoints _ _ (T121_20 i) (hfix121_20 i) _)
      ⟨121, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T121_20_2 Q2.hfix121_20_2 Q2.hinj121_20_2
      Q2.hcardT121_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_20_2 i) (Q2.hfix121_20_2 i) _)
      colCert_121_20_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T121_20
      hfix121_20 hinj121_20 hcardT121_20
      (fun i => conj_mem_of_fixedPoints _ _ (T121_20 i) (hfix121_20 i) _)
      ⟨121, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T121_20_2 Q2.hfix121_20_2 Q2.hinj121_20_2
      Q2.hcardT121_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_20_2 i) (Q2.hfix121_20_2 i) _)
      colCert_121_20_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T121_20
      hfix121_20 hinj121_20 hcardT121_20
      (fun i => conj_mem_of_fixedPoints _ _ (T121_20 i) (hfix121_20 i) _)
      ⟨121, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T121_20_2 Q2.hfix121_20_2 Q2.hinj121_20_2
      Q2.hcardT121_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_20_2 i) (Q2.hfix121_20_2 i) _)
      colCert_121_20_5.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T121_20
      hfix121_20 hinj121_20 hcardT121_20
      (fun i => conj_mem_of_fixedPoints _ _ (T121_20 i) (hfix121_20 i) _)
      ⟨121, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T121_20_2 Q2.hfix121_20_2 Q2.hinj121_20_2
      Q2.hcardT121_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_20_2 i) (Q2.hfix121_20_2 i) _)
      colCert_121_20_10.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T121_20
      hfix121_20 hinj121_20 hcardT121_20
      (fun i => conj_mem_of_fixedPoints _ _ (T121_20 i) (hfix121_20 i) _)
      ⟨121, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T121_20_2 Q2.hfix121_20_2 Q2.hinj121_20_2
      Q2.hcardT121_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_20_2 i) (Q2.hfix121_20_2 i) _)
      colCert_121_20_15.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T121_20
      hfix121_20 hinj121_20 hcardT121_20
      (fun i => conj_mem_of_fixedPoints _ _ (T121_20 i) (hfix121_20 i) _)
      ⟨121, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T121_20_2 Q2.hfix121_20_2 Q2.hinj121_20_2
      Q2.hcardT121_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_20_2 i) (Q2.hfix121_20_2 i) _)
      colCert_121_20_20.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T121_32
      hfix121_32 hinj121_32 hcardT121_32
      (fun i => conj_mem_of_fixedPoints _ _ (T121_32 i) (hfix121_32 i) _)
      ⟨121, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T121_32_2 Q2.hfix121_32_2 Q2.hinj121_32_2
      Q2.hcardT121_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_32_2 i) (Q2.hfix121_32_2 i) _)
      colCert_121_32_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T121_32
      hfix121_32 hinj121_32 hcardT121_32
      (fun i => conj_mem_of_fixedPoints _ _ (T121_32 i) (hfix121_32 i) _)
      ⟨121, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T121_32_2 Q2.hfix121_32_2 Q2.hinj121_32_2
      Q2.hcardT121_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_32_2 i) (Q2.hfix121_32_2 i) _)
      colCert_121_32_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T121_32
      hfix121_32 hinj121_32 hcardT121_32
      (fun i => conj_mem_of_fixedPoints _ _ (T121_32 i) (hfix121_32 i) _)
      ⟨121, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T121_32_2 Q2.hfix121_32_2 Q2.hinj121_32_2
      Q2.hcardT121_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_32_2 i) (Q2.hfix121_32_2 i) _)
      colCert_121_32_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T121_32
      hfix121_32 hinj121_32 hcardT121_32
      (fun i => conj_mem_of_fixedPoints _ _ (T121_32 i) (hfix121_32 i) _)
      ⟨121, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T121_32_2 Q2.hfix121_32_2 Q2.hinj121_32_2
      Q2.hcardT121_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_32_2 i) (Q2.hfix121_32_2 i) _)
      colCert_121_32_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T121_32
      hfix121_32 hinj121_32 hcardT121_32
      (fun i => conj_mem_of_fixedPoints _ _ (T121_32 i) (hfix121_32 i) _)
      ⟨121, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T121_32_2 Q2.hfix121_32_2 Q2.hinj121_32_2
      Q2.hcardT121_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_32_2 i) (Q2.hfix121_32_2 i) _)
      colCert_121_32_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T121_32
      hfix121_32 hinj121_32 hcardT121_32
      (fun i => conj_mem_of_fixedPoints _ _ (T121_32 i) (hfix121_32 i) _)
      ⟨121, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T121_32_2 Q2.hfix121_32_2 Q2.hinj121_32_2
      Q2.hcardT121_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_32_2 i) (Q2.hfix121_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T121_32 = colFn colCertDiv_121_32_5.D1 (m := 5) from colCertDiv_121_32_5.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 5 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T121_32_2 = colFn colCertDiv_121_32_5.D2 (m := 5) from colCertDiv_121_32_5.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_32_5_match


theorem leaf_121_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T121_32
      hfix121_32 hinj121_32 hcardT121_32
      (fun i => conj_mem_of_fixedPoints _ _ (T121_32 i) (hfix121_32 i) _)
      ⟨121, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T121_32_2 Q2.hfix121_32_2 Q2.hinj121_32_2
      Q2.hcardT121_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_32_2 i) (Q2.hfix121_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T121_32 = colFn colCertDiv_121_32_10.D1 (m := 5) from colCertDiv_121_32_10.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 10 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T121_32_2 = colFn colCertDiv_121_32_10.D2 (m := 5) from colCertDiv_121_32_10.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_32_10_match


theorem leaf_121_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T121_32
      hfix121_32 hinj121_32 hcardT121_32
      (fun i => conj_mem_of_fixedPoints _ _ (T121_32 i) (hfix121_32 i) _)
      ⟨121, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T121_32_2 Q2.hfix121_32_2 Q2.hinj121_32_2
      Q2.hcardT121_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_32_2 i) (Q2.hfix121_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T121_32 = colFn colCertDiv_121_32_15.D1 (m := 5) from colCertDiv_121_32_15.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 15 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T121_32_2 = colFn colCertDiv_121_32_15.D2 (m := 5) from colCertDiv_121_32_15.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_32_15_match


theorem leaf_121_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T121_32
      hfix121_32 hinj121_32 hcardT121_32
      (fun i => conj_mem_of_fixedPoints _ _ (T121_32 i) (hfix121_32 i) _)
      ⟨121, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T121_32_2 Q2.hfix121_32_2 Q2.hinj121_32_2
      Q2.hcardT121_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_32_2 i) (Q2.hfix121_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T121_32 = colFn colCertDiv_121_32_20.D1 (m := 5) from colCertDiv_121_32_20.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 20 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T121_32_2 = colFn colCertDiv_121_32_20.D2 (m := 5) from colCertDiv_121_32_20.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_32_20_match


theorem leaf_121_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T121_35
      hfix121_35 hinj121_35 hcardT121_35
      (fun i => conj_mem_of_fixedPoints _ _ (T121_35 i) (hfix121_35 i) _)
      ⟨121, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T121_35_2 Q2.hfix121_35_2 Q2.hinj121_35_2
      Q2.hcardT121_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_35_2 i) (Q2.hfix121_35_2 i) _)
      colCert_121_35_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T121_35
      hfix121_35 hinj121_35 hcardT121_35
      (fun i => conj_mem_of_fixedPoints _ _ (T121_35 i) (hfix121_35 i) _)
      ⟨121, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T121_35_2 Q2.hfix121_35_2 Q2.hinj121_35_2
      Q2.hcardT121_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_35_2 i) (Q2.hfix121_35_2 i) _)
      colCert_121_35_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T121_35
      hfix121_35 hinj121_35 hcardT121_35
      (fun i => conj_mem_of_fixedPoints _ _ (T121_35 i) (hfix121_35 i) _)
      ⟨121, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T121_35_2 Q2.hfix121_35_2 Q2.hinj121_35_2
      Q2.hcardT121_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_35_2 i) (Q2.hfix121_35_2 i) _)
      colCert_121_35_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T121_35
      hfix121_35 hinj121_35 hcardT121_35
      (fun i => conj_mem_of_fixedPoints _ _ (T121_35 i) (hfix121_35 i) _)
      ⟨121, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T121_35_2 Q2.hfix121_35_2 Q2.hinj121_35_2
      Q2.hcardT121_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_35_2 i) (Q2.hfix121_35_2 i) _)
      colCert_121_35_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T121_35
      hfix121_35 hinj121_35 hcardT121_35
      (fun i => conj_mem_of_fixedPoints _ _ (T121_35 i) (hfix121_35 i) _)
      ⟨121, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T121_35_2 Q2.hfix121_35_2 Q2.hinj121_35_2
      Q2.hcardT121_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_35_2 i) (Q2.hfix121_35_2 i) _)
      colCert_121_35_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T121_35
      hfix121_35 hinj121_35 hcardT121_35
      (fun i => conj_mem_of_fixedPoints _ _ (T121_35 i) (hfix121_35 i) _)
      ⟨121, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T121_35_2 Q2.hfix121_35_2 Q2.hinj121_35_2
      Q2.hcardT121_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_35_2 i) (Q2.hfix121_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T121_35 = colFn colCertDiv_121_35_5.D1 (m := 5) from colCertDiv_121_35_5.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 5 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T121_35_2 = colFn colCertDiv_121_35_5.D2 (m := 5) from colCertDiv_121_35_5.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_35_5_match


theorem leaf_121_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T121_35
      hfix121_35 hinj121_35 hcardT121_35
      (fun i => conj_mem_of_fixedPoints _ _ (T121_35 i) (hfix121_35 i) _)
      ⟨121, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T121_35_2 Q2.hfix121_35_2 Q2.hinj121_35_2
      Q2.hcardT121_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_35_2 i) (Q2.hfix121_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T121_35 = colFn colCertDiv_121_35_10.D1 (m := 5) from colCertDiv_121_35_10.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 10 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T121_35_2 = colFn colCertDiv_121_35_10.D2 (m := 5) from colCertDiv_121_35_10.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_35_10_match


theorem leaf_121_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T121_35
      hfix121_35 hinj121_35 hcardT121_35
      (fun i => conj_mem_of_fixedPoints _ _ (T121_35 i) (hfix121_35 i) _)
      ⟨121, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T121_35_2 Q2.hfix121_35_2 Q2.hinj121_35_2
      Q2.hcardT121_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_35_2 i) (Q2.hfix121_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T121_35 = colFn colCertDiv_121_35_15.D1 (m := 5) from colCertDiv_121_35_15.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 15 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T121_35_2 = colFn colCertDiv_121_35_15.D2 (m := 5) from colCertDiv_121_35_15.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_35_15_match


theorem leaf_121_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T121_35
      hfix121_35 hinj121_35 hcardT121_35
      (fun i => conj_mem_of_fixedPoints _ _ (T121_35 i) (hfix121_35 i) _)
      ⟨121, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T121_35_2 Q2.hfix121_35_2 Q2.hinj121_35_2
      Q2.hcardT121_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_35_2 i) (Q2.hfix121_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T121_35 = colFn colCertDiv_121_35_20.D1 (m := 5) from colCertDiv_121_35_20.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 20 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T121_35_2 = colFn colCertDiv_121_35_20.D2 (m := 5) from colCertDiv_121_35_20.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_35_20_match


theorem leaf_121_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T121_41
      hfix121_41 hinj121_41 hcardT121_41
      (fun i => conj_mem_of_fixedPoints _ _ (T121_41 i) (hfix121_41 i) _)
      ⟨121, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T121_41_2 Q2.hfix121_41_2 Q2.hinj121_41_2
      Q2.hcardT121_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_41_2 i) (Q2.hfix121_41_2 i) _)
      colCert_121_41_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T121_41
      hfix121_41 hinj121_41 hcardT121_41
      (fun i => conj_mem_of_fixedPoints _ _ (T121_41 i) (hfix121_41 i) _)
      ⟨121, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T121_41_2 Q2.hfix121_41_2 Q2.hinj121_41_2
      Q2.hcardT121_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_41_2 i) (Q2.hfix121_41_2 i) _)
      colCert_121_41_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T121_41
      hfix121_41 hinj121_41 hcardT121_41
      (fun i => conj_mem_of_fixedPoints _ _ (T121_41 i) (hfix121_41 i) _)
      ⟨121, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T121_41_2 Q2.hfix121_41_2 Q2.hinj121_41_2
      Q2.hcardT121_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_41_2 i) (Q2.hfix121_41_2 i) _)
      colCert_121_41_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T121_41
      hfix121_41 hinj121_41 hcardT121_41
      (fun i => conj_mem_of_fixedPoints _ _ (T121_41 i) (hfix121_41 i) _)
      ⟨121, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T121_41_2 Q2.hfix121_41_2 Q2.hinj121_41_2
      Q2.hcardT121_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_41_2 i) (Q2.hfix121_41_2 i) _)
      colCert_121_41_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T121_41
      hfix121_41 hinj121_41 hcardT121_41
      (fun i => conj_mem_of_fixedPoints _ _ (T121_41 i) (hfix121_41 i) _)
      ⟨121, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T121_41_2 Q2.hfix121_41_2 Q2.hinj121_41_2
      Q2.hcardT121_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_41_2 i) (Q2.hfix121_41_2 i) _)
      colCert_121_41_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T121_41
      hfix121_41 hinj121_41 hcardT121_41
      (fun i => conj_mem_of_fixedPoints _ _ (T121_41 i) (hfix121_41 i) _)
      ⟨121, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T121_41_2 Q2.hfix121_41_2 Q2.hinj121_41_2
      Q2.hcardT121_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_41_2 i) (Q2.hfix121_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T121_41 = colFn colCertDiv_121_41_5.D1 (m := 5) from colCertDiv_121_41_5.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 5 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T121_41_2 = colFn colCertDiv_121_41_5.D2 (m := 5) from colCertDiv_121_41_5.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_41_5_match


theorem leaf_121_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T121_41
      hfix121_41 hinj121_41 hcardT121_41
      (fun i => conj_mem_of_fixedPoints _ _ (T121_41 i) (hfix121_41 i) _)
      ⟨121, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T121_41_2 Q2.hfix121_41_2 Q2.hinj121_41_2
      Q2.hcardT121_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_41_2 i) (Q2.hfix121_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T121_41 = colFn colCertDiv_121_41_10.D1 (m := 5) from colCertDiv_121_41_10.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 10 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T121_41_2 = colFn colCertDiv_121_41_10.D2 (m := 5) from colCertDiv_121_41_10.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_41_10_match


theorem leaf_121_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T121_41
      hfix121_41 hinj121_41 hcardT121_41
      (fun i => conj_mem_of_fixedPoints _ _ (T121_41 i) (hfix121_41 i) _)
      ⟨121, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T121_41_2 Q2.hfix121_41_2 Q2.hinj121_41_2
      Q2.hcardT121_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_41_2 i) (Q2.hfix121_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T121_41 = colFn colCertDiv_121_41_15.D1 (m := 5) from colCertDiv_121_41_15.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 15 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T121_41_2 = colFn colCertDiv_121_41_15.D2 (m := 5) from colCertDiv_121_41_15.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_41_15_match


theorem leaf_121_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T121_41
      hfix121_41 hinj121_41 hcardT121_41
      (fun i => conj_mem_of_fixedPoints _ _ (T121_41 i) (hfix121_41 i) _)
      ⟨121, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T121_41_2 Q2.hfix121_41_2 Q2.hinj121_41_2
      Q2.hcardT121_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_41_2 i) (Q2.hfix121_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T121_41 = colFn colCertDiv_121_41_20.D1 (m := 5) from colCertDiv_121_41_20.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 20 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T121_41_2 = colFn colCertDiv_121_41_20.D2 (m := 5) from colCertDiv_121_41_20.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_41_20_match


theorem leaf_121_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T121_44
      hfix121_44 hinj121_44 hcardT121_44
      (fun i => conj_mem_of_fixedPoints _ _ (T121_44 i) (hfix121_44 i) _)
      ⟨121, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T121_44_2 Q2.hfix121_44_2 Q2.hinj121_44_2
      Q2.hcardT121_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_44_2 i) (Q2.hfix121_44_2 i) _)
      colCert_121_44_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T121_44
      hfix121_44 hinj121_44 hcardT121_44
      (fun i => conj_mem_of_fixedPoints _ _ (T121_44 i) (hfix121_44 i) _)
      ⟨121, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T121_44_2 Q2.hfix121_44_2 Q2.hinj121_44_2
      Q2.hcardT121_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_44_2 i) (Q2.hfix121_44_2 i) _)
      colCert_121_44_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T121_44
      hfix121_44 hinj121_44 hcardT121_44
      (fun i => conj_mem_of_fixedPoints _ _ (T121_44 i) (hfix121_44 i) _)
      ⟨121, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T121_44_2 Q2.hfix121_44_2 Q2.hinj121_44_2
      Q2.hcardT121_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_44_2 i) (Q2.hfix121_44_2 i) _)
      colCert_121_44_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T121_44
      hfix121_44 hinj121_44 hcardT121_44
      (fun i => conj_mem_of_fixedPoints _ _ (T121_44 i) (hfix121_44 i) _)
      ⟨121, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T121_44_2 Q2.hfix121_44_2 Q2.hinj121_44_2
      Q2.hcardT121_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_44_2 i) (Q2.hfix121_44_2 i) _)
      colCert_121_44_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T121_44
      hfix121_44 hinj121_44 hcardT121_44
      (fun i => conj_mem_of_fixedPoints _ _ (T121_44 i) (hfix121_44 i) _)
      ⟨121, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T121_44_2 Q2.hfix121_44_2 Q2.hinj121_44_2
      Q2.hcardT121_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_44_2 i) (Q2.hfix121_44_2 i) _)
      colCert_121_44_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T121_44
      hfix121_44 hinj121_44 hcardT121_44
      (fun i => conj_mem_of_fixedPoints _ _ (T121_44 i) (hfix121_44 i) _)
      ⟨121, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T121_44_2 Q2.hfix121_44_2 Q2.hinj121_44_2
      Q2.hcardT121_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_44_2 i) (Q2.hfix121_44_2 i) _)
      colCert_121_44_5.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T121_44
      hfix121_44 hinj121_44 hcardT121_44
      (fun i => conj_mem_of_fixedPoints _ _ (T121_44 i) (hfix121_44 i) _)
      ⟨121, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T121_44_2 Q2.hfix121_44_2 Q2.hinj121_44_2
      Q2.hcardT121_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_44_2 i) (Q2.hfix121_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T121_44 = colFn colCertDiv_121_44_10.D1 (m := 5) from colCertDiv_121_44_10.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 10 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T121_44_2 = colFn colCertDiv_121_44_10.D2 (m := 5) from colCertDiv_121_44_10.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_44_10_match


theorem leaf_121_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T121_44
      hfix121_44 hinj121_44 hcardT121_44
      (fun i => conj_mem_of_fixedPoints _ _ (T121_44 i) (hfix121_44 i) _)
      ⟨121, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T121_44_2 Q2.hfix121_44_2 Q2.hinj121_44_2
      Q2.hcardT121_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_44_2 i) (Q2.hfix121_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T121_44 = colFn colCertDiv_121_44_15.D1 (m := 5) from colCertDiv_121_44_15.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 15 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T121_44_2 = colFn colCertDiv_121_44_15.D2 (m := 5) from colCertDiv_121_44_15.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_44_15_match


theorem leaf_121_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T121_44
      hfix121_44 hinj121_44 hcardT121_44
      (fun i => conj_mem_of_fixedPoints _ _ (T121_44 i) (hfix121_44 i) _)
      ⟨121, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T121_44_2 Q2.hfix121_44_2 Q2.hinj121_44_2
      Q2.hcardT121_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_44_2 i) (Q2.hfix121_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T121_44 = colFn colCertDiv_121_44_20.D1 (m := 5) from colCertDiv_121_44_20.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 20 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T121_44_2 = colFn colCertDiv_121_44_20.D2 (m := 5) from colCertDiv_121_44_20.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_44_20_match


theorem leaf_121_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T121_48
      hfix121_48 hinj121_48 hcardT121_48
      (fun i => conj_mem_of_fixedPoints _ _ (T121_48 i) (hfix121_48 i) _)
      ⟨121, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T121_48_2 Q2.hfix121_48_2 Q2.hinj121_48_2
      Q2.hcardT121_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_48_2 i) (Q2.hfix121_48_2 i) _)
      colCert_121_48_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T121_48
      hfix121_48 hinj121_48 hcardT121_48
      (fun i => conj_mem_of_fixedPoints _ _ (T121_48 i) (hfix121_48 i) _)
      ⟨121, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T121_48_2 Q2.hfix121_48_2 Q2.hinj121_48_2
      Q2.hcardT121_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_48_2 i) (Q2.hfix121_48_2 i) _)
      colCert_121_48_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T121_48
      hfix121_48 hinj121_48 hcardT121_48
      (fun i => conj_mem_of_fixedPoints _ _ (T121_48 i) (hfix121_48 i) _)
      ⟨121, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T121_48_2 Q2.hfix121_48_2 Q2.hinj121_48_2
      Q2.hcardT121_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_48_2 i) (Q2.hfix121_48_2 i) _)
      colCert_121_48_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T121_48
      hfix121_48 hinj121_48 hcardT121_48
      (fun i => conj_mem_of_fixedPoints _ _ (T121_48 i) (hfix121_48 i) _)
      ⟨121, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T121_48_2 Q2.hfix121_48_2 Q2.hinj121_48_2
      Q2.hcardT121_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_48_2 i) (Q2.hfix121_48_2 i) _)
      colCert_121_48_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T121_48
      hfix121_48 hinj121_48 hcardT121_48
      (fun i => conj_mem_of_fixedPoints _ _ (T121_48 i) (hfix121_48 i) _)
      ⟨121, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T121_48_2 Q2.hfix121_48_2 Q2.hinj121_48_2
      Q2.hcardT121_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_48_2 i) (Q2.hfix121_48_2 i) _)
      colCert_121_48_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T121_48
      hfix121_48 hinj121_48 hcardT121_48
      (fun i => conj_mem_of_fixedPoints _ _ (T121_48 i) (hfix121_48 i) _)
      ⟨121, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T121_48_2 Q2.hfix121_48_2 Q2.hinj121_48_2
      Q2.hcardT121_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_48_2 i) (Q2.hfix121_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T121_48 = colFn colCertDiv_121_48_5.D1 (m := 5) from colCertDiv_121_48_5.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T121_48_2 = colFn colCertDiv_121_48_5.D2 (m := 5) from colCertDiv_121_48_5.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_48_5_match


theorem leaf_121_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T121_48
      hfix121_48 hinj121_48 hcardT121_48
      (fun i => conj_mem_of_fixedPoints _ _ (T121_48 i) (hfix121_48 i) _)
      ⟨121, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T121_48_2 Q2.hfix121_48_2 Q2.hinj121_48_2
      Q2.hcardT121_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_48_2 i) (Q2.hfix121_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T121_48 = colFn colCertDiv_121_48_10.D1 (m := 5) from colCertDiv_121_48_10.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T121_48_2 = colFn colCertDiv_121_48_10.D2 (m := 5) from colCertDiv_121_48_10.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_48_10_match


theorem leaf_121_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T121_48
      hfix121_48 hinj121_48 hcardT121_48
      (fun i => conj_mem_of_fixedPoints _ _ (T121_48 i) (hfix121_48 i) _)
      ⟨121, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T121_48_2 Q2.hfix121_48_2 Q2.hinj121_48_2
      Q2.hcardT121_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_48_2 i) (Q2.hfix121_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T121_48 = colFn colCertDiv_121_48_15.D1 (m := 5) from colCertDiv_121_48_15.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T121_48_2 = colFn colCertDiv_121_48_15.D2 (m := 5) from colCertDiv_121_48_15.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_48_15_match


theorem leaf_121_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T121_48
      hfix121_48 hinj121_48 hcardT121_48
      (fun i => conj_mem_of_fixedPoints _ _ (T121_48 i) (hfix121_48 i) _)
      ⟨121, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T121_48_2 Q2.hfix121_48_2 Q2.hinj121_48_2
      Q2.hcardT121_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_48_2 i) (Q2.hfix121_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T121_48 = colFn colCertDiv_121_48_20.D1 (m := 5) from colCertDiv_121_48_20.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T121_48_2 = colFn colCertDiv_121_48_20.D2 (m := 5) from colCertDiv_121_48_20.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_48_20_match


theorem leaf_121_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T121_53
      hfix121_53 hinj121_53 hcardT121_53
      (fun i => conj_mem_of_fixedPoints _ _ (T121_53 i) (hfix121_53 i) _)
      ⟨121, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T121_53_2 Q2.hfix121_53_2 Q2.hinj121_53_2
      Q2.hcardT121_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_53_2 i) (Q2.hfix121_53_2 i) _)
      colCert_121_53_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T121_53
      hfix121_53 hinj121_53 hcardT121_53
      (fun i => conj_mem_of_fixedPoints _ _ (T121_53 i) (hfix121_53 i) _)
      ⟨121, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T121_53_2 Q2.hfix121_53_2 Q2.hinj121_53_2
      Q2.hcardT121_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_53_2 i) (Q2.hfix121_53_2 i) _)
      colCert_121_53_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T121_53
      hfix121_53 hinj121_53 hcardT121_53
      (fun i => conj_mem_of_fixedPoints _ _ (T121_53 i) (hfix121_53 i) _)
      ⟨121, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T121_53_2 Q2.hfix121_53_2 Q2.hinj121_53_2
      Q2.hcardT121_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_53_2 i) (Q2.hfix121_53_2 i) _)
      colCert_121_53_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T121_53
      hfix121_53 hinj121_53 hcardT121_53
      (fun i => conj_mem_of_fixedPoints _ _ (T121_53 i) (hfix121_53 i) _)
      ⟨121, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T121_53_2 Q2.hfix121_53_2 Q2.hinj121_53_2
      Q2.hcardT121_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_53_2 i) (Q2.hfix121_53_2 i) _)
      colCert_121_53_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T121_53
      hfix121_53 hinj121_53 hcardT121_53
      (fun i => conj_mem_of_fixedPoints _ _ (T121_53 i) (hfix121_53 i) _)
      ⟨121, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T121_53_2 Q2.hfix121_53_2 Q2.hinj121_53_2
      Q2.hcardT121_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_53_2 i) (Q2.hfix121_53_2 i) _)
      colCert_121_53_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T121_53
      hfix121_53 hinj121_53 hcardT121_53
      (fun i => conj_mem_of_fixedPoints _ _ (T121_53 i) (hfix121_53 i) _)
      ⟨121, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T121_53_2 Q2.hfix121_53_2 Q2.hinj121_53_2
      Q2.hcardT121_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_53_2 i) (Q2.hfix121_53_2 i) _)
      colCert_121_53_5.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T121_53
      hfix121_53 hinj121_53 hcardT121_53
      (fun i => conj_mem_of_fixedPoints _ _ (T121_53 i) (hfix121_53 i) _)
      ⟨121, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T121_53_2 Q2.hfix121_53_2 Q2.hinj121_53_2
      Q2.hcardT121_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_53_2 i) (Q2.hfix121_53_2 i) _)
      colCert_121_53_10.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T121_53
      hfix121_53 hinj121_53 hcardT121_53
      (fun i => conj_mem_of_fixedPoints _ _ (T121_53 i) (hfix121_53 i) _)
      ⟨121, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T121_53_2 Q2.hfix121_53_2 Q2.hinj121_53_2
      Q2.hcardT121_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_53_2 i) (Q2.hfix121_53_2 i) _)
      colCert_121_53_15.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T121_53
      hfix121_53 hinj121_53 hcardT121_53
      (fun i => conj_mem_of_fixedPoints _ _ (T121_53 i) (hfix121_53 i) _)
      ⟨121, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T121_53_2 Q2.hfix121_53_2 Q2.hinj121_53_2
      Q2.hcardT121_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_53_2 i) (Q2.hfix121_53_2 i) _)
      colCert_121_53_20.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_81_0 (hp : 0 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp)) T121_81
      hfix121_81 hinj121_81 hcardT121_81
      (fun i => conj_mem_of_fixedPoints _ _ (T121_81 i) (hfix121_81 i) _)
      ⟨121, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 0 hp) Q2.T121_81_2 Q2.hfix121_81_2 Q2.hinj121_81_2
      Q2.hcardT121_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_81_2 i) (Q2.hfix121_81_2 i) _)
      colCert_121_81_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_81_1 (hp : 1 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp)) T121_81
      hfix121_81 hinj121_81 hcardT121_81
      (fun i => conj_mem_of_fixedPoints _ _ (T121_81 i) (hfix121_81 i) _)
      ⟨121, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 1 hp) Q2.T121_81_2 Q2.hfix121_81_2 Q2.hinj121_81_2
      Q2.hcardT121_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_81_2 i) (Q2.hfix121_81_2 i) _)
      colCert_121_81_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_81_2 (hp : 2 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp)) T121_81
      hfix121_81 hinj121_81 hcardT121_81
      (fun i => conj_mem_of_fixedPoints _ _ (T121_81 i) (hfix121_81 i) _)
      ⟨121, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 2 hp) Q2.T121_81_2 Q2.hfix121_81_2 Q2.hinj121_81_2
      Q2.hcardT121_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_81_2 i) (Q2.hfix121_81_2 i) _)
      colCert_121_81_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_81_3 (hp : 3 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp)) T121_81
      hfix121_81 hinj121_81 hcardT121_81
      (fun i => conj_mem_of_fixedPoints _ _ (T121_81 i) (hfix121_81 i) _)
      ⟨121, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 3 hp) Q2.T121_81_2 Q2.hfix121_81_2 Q2.hinj121_81_2
      Q2.hcardT121_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_81_2 i) (Q2.hfix121_81_2 i) _)
      colCert_121_81_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_81_4 (hp : 4 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp)) T121_81
      hfix121_81 hinj121_81 hcardT121_81
      (fun i => conj_mem_of_fixedPoints _ _ (T121_81 i) (hfix121_81 i) _)
      ⟨121, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 4 hp) Q2.T121_81_2 Q2.hfix121_81_2 Q2.hinj121_81_2
      Q2.hcardT121_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_81_2 i) (Q2.hfix121_81_2 i) _)
      colCert_121_81_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_81_5 (hp : 5 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp)) T121_81
      hfix121_81 hinj121_81 hcardT121_81
      (fun i => conj_mem_of_fixedPoints _ _ (T121_81 i) (hfix121_81 i) _)
      ⟨121, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 5 hp) Q2.T121_81_2 Q2.hfix121_81_2 Q2.hinj121_81_2
      Q2.hcardT121_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_81_2 i) (Q2.hfix121_81_2 i) _)
      colCert_121_81_5.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_81_10 (hp : 10 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp)) T121_81
      hfix121_81 hinj121_81 hcardT121_81
      (fun i => conj_mem_of_fixedPoints _ _ (T121_81 i) (hfix121_81 i) _)
      ⟨121, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 10 hp) Q2.T121_81_2 Q2.hfix121_81_2 Q2.hinj121_81_2
      Q2.hcardT121_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_81_2 i) (Q2.hfix121_81_2 i) _)
      colCert_121_81_10.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_81_15 (hp : 15 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp)) T121_81
      hfix121_81 hinj121_81 hcardT121_81
      (fun i => conj_mem_of_fixedPoints _ _ (T121_81 i) (hfix121_81 i) _)
      ⟨121, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 15 hp) Q2.T121_81_2 Q2.hfix121_81_2 Q2.hinj121_81_2
      Q2.hcardT121_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_81_2 i) (Q2.hfix121_81_2 i) _)
      colCert_121_81_15.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_81_20 (hp : 20 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp)) T121_81
      hfix121_81 hinj121_81 hcardT121_81
      (fun i => conj_mem_of_fixedPoints _ _ (T121_81 i) (hfix121_81 i) _)
      ⟨121, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 20 hp) Q2.T121_81_2 Q2.hfix121_81_2 Q2.hinj121_81_2
      Q2.hcardT121_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_81_2 i) (Q2.hfix121_81_2 i) _)
      colCert_121_81_20.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_94_0 (hp : 0 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp)) T121_94
      hfix121_94 hinj121_94 hcardT121_94
      (fun i => conj_mem_of_fixedPoints _ _ (T121_94 i) (hfix121_94 i) _)
      ⟨121, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 0 hp) Q2.T121_94_2 Q2.hfix121_94_2 Q2.hinj121_94_2
      Q2.hcardT121_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_94_2 i) (Q2.hfix121_94_2 i) _)
      colCert_121_94_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_94_1 (hp : 1 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp)) T121_94
      hfix121_94 hinj121_94 hcardT121_94
      (fun i => conj_mem_of_fixedPoints _ _ (T121_94 i) (hfix121_94 i) _)
      ⟨121, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 1 hp) Q2.T121_94_2 Q2.hfix121_94_2 Q2.hinj121_94_2
      Q2.hcardT121_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_94_2 i) (Q2.hfix121_94_2 i) _)
      colCert_121_94_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_94_2 (hp : 2 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp)) T121_94
      hfix121_94 hinj121_94 hcardT121_94
      (fun i => conj_mem_of_fixedPoints _ _ (T121_94 i) (hfix121_94 i) _)
      ⟨121, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 2 hp) Q2.T121_94_2 Q2.hfix121_94_2 Q2.hinj121_94_2
      Q2.hcardT121_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_94_2 i) (Q2.hfix121_94_2 i) _)
      colCert_121_94_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_94_3 (hp : 3 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp)) T121_94
      hfix121_94 hinj121_94 hcardT121_94
      (fun i => conj_mem_of_fixedPoints _ _ (T121_94 i) (hfix121_94 i) _)
      ⟨121, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 3 hp) Q2.T121_94_2 Q2.hfix121_94_2 Q2.hinj121_94_2
      Q2.hcardT121_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_94_2 i) (Q2.hfix121_94_2 i) _)
      colCert_121_94_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_94_4 (hp : 4 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp)) T121_94
      hfix121_94 hinj121_94 hcardT121_94
      (fun i => conj_mem_of_fixedPoints _ _ (T121_94 i) (hfix121_94 i) _)
      ⟨121, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 4 hp) Q2.T121_94_2 Q2.hfix121_94_2 Q2.hinj121_94_2
      Q2.hcardT121_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_94_2 i) (Q2.hfix121_94_2 i) _)
      colCert_121_94_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_94_5 (hp : 5 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp)) T121_94
      hfix121_94 hinj121_94 hcardT121_94
      (fun i => conj_mem_of_fixedPoints _ _ (T121_94 i) (hfix121_94 i) _)
      ⟨121, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 5 hp) Q2.T121_94_2 Q2.hfix121_94_2 Q2.hinj121_94_2
      Q2.hcardT121_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_94_2 i) (Q2.hfix121_94_2 i) _)
      colCert_121_94_5.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_94_10 (hp : 10 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp)) T121_94
      hfix121_94 hinj121_94 hcardT121_94
      (fun i => conj_mem_of_fixedPoints _ _ (T121_94 i) (hfix121_94 i) _)
      ⟨121, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 10 hp) Q2.T121_94_2 Q2.hfix121_94_2 Q2.hinj121_94_2
      Q2.hcardT121_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_94_2 i) (Q2.hfix121_94_2 i) _)
      colCert_121_94_10.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_94_15 (hp : 15 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp)) T121_94
      hfix121_94 hinj121_94 hcardT121_94
      (fun i => conj_mem_of_fixedPoints _ _ (T121_94 i) (hfix121_94 i) _)
      ⟨121, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 15 hp) Q2.T121_94_2 Q2.hfix121_94_2 Q2.hinj121_94_2
      Q2.hcardT121_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_94_2 i) (Q2.hfix121_94_2 i) _)
      colCert_121_94_15.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_94_20 (hp : 20 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp)) T121_94
      hfix121_94 hinj121_94 hcardT121_94
      (fun i => conj_mem_of_fixedPoints _ _ (T121_94 i) (hfix121_94 i) _)
      ⟨121, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 20 hp) Q2.T121_94_2 Q2.hfix121_94_2 Q2.hinj121_94_2
      Q2.hcardT121_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_94_2 i) (Q2.hfix121_94_2 i) _)
      colCert_121_94_20.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_97_0 (hp : 0 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp)) T121_97
      hfix121_97 hinj121_97 hcardT121_97
      (fun i => conj_mem_of_fixedPoints _ _ (T121_97 i) (hfix121_97 i) _)
      ⟨121, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 0 hp) Q2.T121_97_2 Q2.hfix121_97_2 Q2.hinj121_97_2
      Q2.hcardT121_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_97_2 i) (Q2.hfix121_97_2 i) _)
      colCert_121_97_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_97_1 (hp : 1 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp)) T121_97
      hfix121_97 hinj121_97 hcardT121_97
      (fun i => conj_mem_of_fixedPoints _ _ (T121_97 i) (hfix121_97 i) _)
      ⟨121, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 1 hp) Q2.T121_97_2 Q2.hfix121_97_2 Q2.hinj121_97_2
      Q2.hcardT121_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_97_2 i) (Q2.hfix121_97_2 i) _)
      colCert_121_97_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_97_2 (hp : 2 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp)) T121_97
      hfix121_97 hinj121_97 hcardT121_97
      (fun i => conj_mem_of_fixedPoints _ _ (T121_97 i) (hfix121_97 i) _)
      ⟨121, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 2 hp) Q2.T121_97_2 Q2.hfix121_97_2 Q2.hinj121_97_2
      Q2.hcardT121_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_97_2 i) (Q2.hfix121_97_2 i) _)
      colCert_121_97_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_97_3 (hp : 3 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp)) T121_97
      hfix121_97 hinj121_97 hcardT121_97
      (fun i => conj_mem_of_fixedPoints _ _ (T121_97 i) (hfix121_97 i) _)
      ⟨121, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 3 hp) Q2.T121_97_2 Q2.hfix121_97_2 Q2.hinj121_97_2
      Q2.hcardT121_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_97_2 i) (Q2.hfix121_97_2 i) _)
      colCert_121_97_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_97_4 (hp : 4 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp)) T121_97
      hfix121_97 hinj121_97 hcardT121_97
      (fun i => conj_mem_of_fixedPoints _ _ (T121_97 i) (hfix121_97 i) _)
      ⟨121, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 4 hp) Q2.T121_97_2 Q2.hfix121_97_2 Q2.hinj121_97_2
      Q2.hcardT121_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_97_2 i) (Q2.hfix121_97_2 i) _)
      colCert_121_97_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_97_5 (hp : 5 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp)) T121_97
      hfix121_97 hinj121_97 hcardT121_97
      (fun i => conj_mem_of_fixedPoints _ _ (T121_97 i) (hfix121_97 i) _)
      ⟨121, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 5 hp) Q2.T121_97_2 Q2.hfix121_97_2 Q2.hinj121_97_2
      Q2.hcardT121_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_97_2 i) (Q2.hfix121_97_2 i) _)
      colCert_121_97_5.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_97_10 (hp : 10 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp)) T121_97
      hfix121_97 hinj121_97 hcardT121_97
      (fun i => conj_mem_of_fixedPoints _ _ (T121_97 i) (hfix121_97 i) _)
      ⟨121, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 10 hp) Q2.T121_97_2 Q2.hfix121_97_2 Q2.hinj121_97_2
      Q2.hcardT121_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_97_2 i) (Q2.hfix121_97_2 i) _)
      colCert_121_97_10.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_97_15 (hp : 15 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp)) T121_97
      hfix121_97 hinj121_97 hcardT121_97
      (fun i => conj_mem_of_fixedPoints _ _ (T121_97 i) (hfix121_97 i) _)
      ⟨121, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 15 hp) Q2.T121_97_2 Q2.hfix121_97_2 Q2.hinj121_97_2
      Q2.hcardT121_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_97_2 i) (Q2.hfix121_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T121_97 = colFn colCertDiv_121_97_15.D1 (m := 5) from colCertDiv_121_97_15.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 15 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T121_97_2 = colFn colCertDiv_121_97_15.D2 (m := 5) from colCertDiv_121_97_15.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_97_15_match


theorem leaf_121_97_20 (hp : 20 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp)) T121_97
      hfix121_97 hinj121_97 hcardT121_97
      (fun i => conj_mem_of_fixedPoints _ _ (T121_97 i) (hfix121_97 i) _)
      ⟨121, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 20 hp) Q2.T121_97_2 Q2.hfix121_97_2 Q2.hinj121_97_2
      Q2.hcardT121_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_97_2 i) (Q2.hfix121_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T121_97 = colFn colCertDiv_121_97_20.D1 (m := 5) from colCertDiv_121_97_20.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 20 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T121_97_2 = colFn colCertDiv_121_97_20.D2 (m := 5) from colCertDiv_121_97_20.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_97_20_match


theorem leaf_121_103_0 (hp : 0 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp)) T121_103
      hfix121_103 hinj121_103 hcardT121_103
      (fun i => conj_mem_of_fixedPoints _ _ (T121_103 i) (hfix121_103 i) _)
      ⟨121, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 0 hp) Q2.T121_103_2 Q2.hfix121_103_2 Q2.hinj121_103_2
      Q2.hcardT121_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_103_2 i) (Q2.hfix121_103_2 i) _)
      colCert_121_103_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_103_1 (hp : 1 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp)) T121_103
      hfix121_103 hinj121_103 hcardT121_103
      (fun i => conj_mem_of_fixedPoints _ _ (T121_103 i) (hfix121_103 i) _)
      ⟨121, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 1 hp) Q2.T121_103_2 Q2.hfix121_103_2 Q2.hinj121_103_2
      Q2.hcardT121_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_103_2 i) (Q2.hfix121_103_2 i) _)
      colCert_121_103_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_103_2 (hp : 2 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp)) T121_103
      hfix121_103 hinj121_103 hcardT121_103
      (fun i => conj_mem_of_fixedPoints _ _ (T121_103 i) (hfix121_103 i) _)
      ⟨121, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 2 hp) Q2.T121_103_2 Q2.hfix121_103_2 Q2.hinj121_103_2
      Q2.hcardT121_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_103_2 i) (Q2.hfix121_103_2 i) _)
      colCert_121_103_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_103_3 (hp : 3 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp)) T121_103
      hfix121_103 hinj121_103 hcardT121_103
      (fun i => conj_mem_of_fixedPoints _ _ (T121_103 i) (hfix121_103 i) _)
      ⟨121, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 3 hp) Q2.T121_103_2 Q2.hfix121_103_2 Q2.hinj121_103_2
      Q2.hcardT121_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_103_2 i) (Q2.hfix121_103_2 i) _)
      colCert_121_103_3.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_103_4 (hp : 4 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 4 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp)) T121_103
      hfix121_103 hinj121_103 hcardT121_103
      (fun i => conj_mem_of_fixedPoints _ _ (T121_103 i) (hfix121_103 i) _)
      ⟨121, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 4 hp) Q2.T121_103_2 Q2.hfix121_103_2 Q2.hinj121_103_2
      Q2.hcardT121_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_103_2 i) (Q2.hfix121_103_2 i) _)
      colCert_121_103_4.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_103_5 (hp : 5 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 5 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp)) T121_103
      hfix121_103 hinj121_103 hcardT121_103
      (fun i => conj_mem_of_fixedPoints _ _ (T121_103 i) (hfix121_103 i) _)
      ⟨121, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 5 hp) Q2.T121_103_2 Q2.hfix121_103_2 Q2.hinj121_103_2
      Q2.hcardT121_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_103_2 i) (Q2.hfix121_103_2 i) _)
      colCert_121_103_5.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_103_10 (hp : 10 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 10 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp)) T121_103
      hfix121_103 hinj121_103 hcardT121_103
      (fun i => conj_mem_of_fixedPoints _ _ (T121_103 i) (hfix121_103 i) _)
      ⟨121, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 10 hp) Q2.T121_103_2 Q2.hfix121_103_2 Q2.hinj121_103_2
      Q2.hcardT121_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_103_2 i) (Q2.hfix121_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T121_103 = colFn colCertDiv_121_103_10.D1 (m := 5) from colCertDiv_121_103_10.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 10 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T121_103_2 = colFn colCertDiv_121_103_10.D2 (m := 5) from colCertDiv_121_103_10.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_103_10_match


theorem leaf_121_103_15 (hp : 15 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 15 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp)) T121_103
      hfix121_103 hinj121_103 hcardT121_103
      (fun i => conj_mem_of_fixedPoints _ _ (T121_103 i) (hfix121_103 i) _)
      ⟨121, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 15 hp) Q2.T121_103_2 Q2.hfix121_103_2 Q2.hinj121_103_2
      Q2.hcardT121_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_103_2 i) (Q2.hfix121_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T121_103 = colFn colCertDiv_121_103_15.D1 (m := 5) from colCertDiv_121_103_15.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 15 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T121_103_2 = colFn colCertDiv_121_103_15.D2 (m := 5) from colCertDiv_121_103_15.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_103_15_match


theorem leaf_121_103_20 (hp : 20 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 20 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨121, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp)) T121_103
      hfix121_103 hinj121_103 hcardT121_103
      (fun i => conj_mem_of_fixedPoints _ _ (T121_103 i) (hfix121_103 i) _)
      ⟨121, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 20 hp) Q2.T121_103_2 Q2.hfix121_103_2 Q2.hinj121_103_2
      Q2.hcardT121_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_103_2 i) (Q2.hfix121_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨121, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T121_103 = colFn colCertDiv_121_103_20.D1 (m := 5) from colCertDiv_121_103_20.bind1,
    show colData2 (⟨121, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 20 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T121_103_2 = colFn colCertDiv_121_103_20.D2 (m := 5) from colCertDiv_121_103_20.bind2]
  rw [alnId_121 j hj]
  exact fastcode_of_div ⟨121, by decide⟩ _ _ _
    ((alnId_121 j hj) ▸ Q2.listedAt (⟨121, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨121, by decide⟩ : Fin 148) hj hq).1) colCertDiv_121_103_20_match


theorem leaf_121_106_0 (hp : 0 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 0 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp)) T121_106
      hfix121_106 hinj121_106 hcardT121_106
      (fun i => conj_mem_of_fixedPoints _ _ (T121_106 i) (hfix121_106 i) _)
      ⟨121, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 0 hp) Q2.T121_106_2 Q2.hfix121_106_2 Q2.hinj121_106_2
      Q2.hcardT121_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_106_2 i) (Q2.hfix121_106_2 i) _)
      colCert_121_106_0.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_106_1 (hp : 1 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 1 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp)) T121_106
      hfix121_106 hinj121_106 hcardT121_106
      (fun i => conj_mem_of_fixedPoints _ _ (T121_106 i) (hfix121_106 i) _)
      ⟨121, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 1 hp) Q2.T121_106_2 Q2.hfix121_106_2 Q2.hinj121_106_2
      Q2.hcardT121_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_106_2 i) (Q2.hfix121_106_2 i) _)
      colCert_121_106_1.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_106_2 (hp : 2 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 2 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp)) T121_106
      hfix121_106 hinj121_106 hcardT121_106
      (fun i => conj_mem_of_fixedPoints _ _ (T121_106 i) (hfix121_106 i) _)
      ⟨121, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 2 hp) Q2.T121_106_2 Q2.hfix121_106_2 Q2.hinj121_106_2
      Q2.hcardT121_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_106_2 i) (Q2.hfix121_106_2 i) _)
      colCert_121_106_2.hD ?_).symm
  rw [alnId_121 j hj]


theorem leaf_121_106_3 (hp : 3 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 121 []).length)
    (hq : (normIsRep.getD 121 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 3 hp)
        (rowE2 (⟨121, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp))
        (rowE1 (⟨121, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨121, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨121, by decide⟩ (listedAt ⟨121, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp)) T121_106
      hfix121_106 hinj121_106 hcardT121_106
      (fun i => conj_mem_of_fixedPoints _ _ (T121_106 i) (hfix121_106 i) _)
      ⟨121, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨121, by decide⟩ (Q2.listedAt ⟨121, by decide⟩
        (alnCheck_rep ⟨121, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 3 hp) Q2.T121_106_2 Q2.hfix121_106_2 Q2.hinj121_106_2
      Q2.hcardT121_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T121_106_2 i) (Q2.hfix121_106_2 i) _)
      colCert_121_106_3.hD ?_).symm
  rw [alnId_121 j hj]


end LeanDring.P5Presentation
