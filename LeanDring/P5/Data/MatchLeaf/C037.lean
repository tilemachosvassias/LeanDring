/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C014
import LeanDring.P5.Data.ColCdd.C015
import LeanDring.P5.Data.ColRestCheap.C067
import LeanDring.P5.Data.ColRestCheap.C068
import LeanDring.P5.Data.ColRestCheap.C069
import LeanDring.P5.Data.ColRestCheap.C070
import LeanDring.P5.Data.EntryK.C034
import LeanDring.P5.Data.EntryK.C035
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C017
import LeanDring.P5.Data.SpeciesDiv.C018
import LeanDring.P5.Data.SpeciesDiv.C019

/-! # Stage-5 leaves, chunk 36 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_131_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T131_10
      hfix131_10 hinj131_10 hcardT131_10
      (fun i => conj_mem_of_fixedPoints _ _ (T131_10 i) (hfix131_10 i) _)
      ⟨131, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T131_10_2 Q2.hfix131_10_2 Q2.hinj131_10_2
      Q2.hcardT131_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_10_2 i) (Q2.hfix131_10_2 i) _)
      colCert_131_10_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T131_10
      hfix131_10 hinj131_10 hcardT131_10
      (fun i => conj_mem_of_fixedPoints _ _ (T131_10 i) (hfix131_10 i) _)
      ⟨131, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T131_10_2 Q2.hfix131_10_2 Q2.hinj131_10_2
      Q2.hcardT131_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_10_2 i) (Q2.hfix131_10_2 i) _)
      colCert_131_10_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T131_12
      hfix131_12 hinj131_12 hcardT131_12
      (fun i => conj_mem_of_fixedPoints _ _ (T131_12 i) (hfix131_12 i) _)
      ⟨131, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T131_12_2 Q2.hfix131_12_2 Q2.hinj131_12_2
      Q2.hcardT131_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_12_2 i) (Q2.hfix131_12_2 i) _)
      colCert_131_12_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T131_12
      hfix131_12 hinj131_12 hcardT131_12
      (fun i => conj_mem_of_fixedPoints _ _ (T131_12 i) (hfix131_12 i) _)
      ⟨131, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T131_12_2 Q2.hfix131_12_2 Q2.hinj131_12_2
      Q2.hcardT131_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_12_2 i) (Q2.hfix131_12_2 i) _)
      colCert_131_12_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T131_12
      hfix131_12 hinj131_12 hcardT131_12
      (fun i => conj_mem_of_fixedPoints _ _ (T131_12 i) (hfix131_12 i) _)
      ⟨131, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T131_12_2 Q2.hfix131_12_2 Q2.hinj131_12_2
      Q2.hcardT131_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_12_2 i) (Q2.hfix131_12_2 i) _)
      colCert_131_12_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T131_12
      hfix131_12 hinj131_12 hcardT131_12
      (fun i => conj_mem_of_fixedPoints _ _ (T131_12 i) (hfix131_12 i) _)
      ⟨131, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T131_12_2 Q2.hfix131_12_2 Q2.hinj131_12_2
      Q2.hcardT131_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_12_2 i) (Q2.hfix131_12_2 i) _)
      colCert_131_12_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T131_12
      hfix131_12 hinj131_12 hcardT131_12
      (fun i => conj_mem_of_fixedPoints _ _ (T131_12 i) (hfix131_12 i) _)
      ⟨131, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T131_12_2 Q2.hfix131_12_2 Q2.hinj131_12_2
      Q2.hcardT131_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_12_2 i) (Q2.hfix131_12_2 i) _)
      colCert_131_12_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T131_22
      hfix131_22 hinj131_22 hcardT131_22
      (fun i => conj_mem_of_fixedPoints _ _ (T131_22 i) (hfix131_22 i) _)
      ⟨131, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T131_22_2 Q2.hfix131_22_2 Q2.hinj131_22_2
      Q2.hcardT131_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_22_2 i) (Q2.hfix131_22_2 i) _)
      colCert_131_22_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T131_22
      hfix131_22 hinj131_22 hcardT131_22
      (fun i => conj_mem_of_fixedPoints _ _ (T131_22 i) (hfix131_22 i) _)
      ⟨131, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T131_22_2 Q2.hfix131_22_2 Q2.hinj131_22_2
      Q2.hcardT131_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_22_2 i) (Q2.hfix131_22_2 i) _)
      colCert_131_22_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T131_22
      hfix131_22 hinj131_22 hcardT131_22
      (fun i => conj_mem_of_fixedPoints _ _ (T131_22 i) (hfix131_22 i) _)
      ⟨131, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T131_22_2 Q2.hfix131_22_2 Q2.hinj131_22_2
      Q2.hcardT131_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_22_2 i) (Q2.hfix131_22_2 i) _)
      colCert_131_22_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T131_22
      hfix131_22 hinj131_22 hcardT131_22
      (fun i => conj_mem_of_fixedPoints _ _ (T131_22 i) (hfix131_22 i) _)
      ⟨131, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T131_22_2 Q2.hfix131_22_2 Q2.hinj131_22_2
      Q2.hcardT131_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_22_2 i) (Q2.hfix131_22_2 i) _)
      colCert_131_22_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T131_22
      hfix131_22 hinj131_22 hcardT131_22
      (fun i => conj_mem_of_fixedPoints _ _ (T131_22 i) (hfix131_22 i) _)
      ⟨131, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T131_22_2 Q2.hfix131_22_2 Q2.hinj131_22_2
      Q2.hcardT131_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_22_2 i) (Q2.hfix131_22_2 i) _)
      colCert_131_22_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T131_22
      hfix131_22 hinj131_22 hcardT131_22
      (fun i => conj_mem_of_fixedPoints _ _ (T131_22 i) (hfix131_22 i) _)
      ⟨131, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T131_22_2 Q2.hfix131_22_2 Q2.hinj131_22_2
      Q2.hcardT131_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_22_2 i) (Q2.hfix131_22_2 i) _)
      colCert_131_22_5.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T131_22
      hfix131_22 hinj131_22 hcardT131_22
      (fun i => conj_mem_of_fixedPoints _ _ (T131_22 i) (hfix131_22 i) _)
      ⟨131, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T131_22_2 Q2.hfix131_22_2 Q2.hinj131_22_2
      Q2.hcardT131_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_22_2 i) (Q2.hfix131_22_2 i) _)
      colCert_131_22_10.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T131_22
      hfix131_22 hinj131_22 hcardT131_22
      (fun i => conj_mem_of_fixedPoints _ _ (T131_22 i) (hfix131_22 i) _)
      ⟨131, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T131_22_2 Q2.hfix131_22_2 Q2.hinj131_22_2
      Q2.hcardT131_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_22_2 i) (Q2.hfix131_22_2 i) _)
      colCert_131_22_15.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T131_22
      hfix131_22 hinj131_22 hcardT131_22
      (fun i => conj_mem_of_fixedPoints _ _ (T131_22 i) (hfix131_22 i) _)
      ⟨131, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T131_22_2 Q2.hfix131_22_2 Q2.hinj131_22_2
      Q2.hcardT131_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_22_2 i) (Q2.hfix131_22_2 i) _)
      colCert_131_22_20.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T131_30
      hfix131_30 hinj131_30 hcardT131_30
      (fun i => conj_mem_of_fixedPoints _ _ (T131_30 i) (hfix131_30 i) _)
      ⟨131, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T131_30_2 Q2.hfix131_30_2 Q2.hinj131_30_2
      Q2.hcardT131_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_30_2 i) (Q2.hfix131_30_2 i) _)
      colCert_131_30_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T131_30
      hfix131_30 hinj131_30 hcardT131_30
      (fun i => conj_mem_of_fixedPoints _ _ (T131_30 i) (hfix131_30 i) _)
      ⟨131, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T131_30_2 Q2.hfix131_30_2 Q2.hinj131_30_2
      Q2.hcardT131_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_30_2 i) (Q2.hfix131_30_2 i) _)
      colCert_131_30_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T131_30
      hfix131_30 hinj131_30 hcardT131_30
      (fun i => conj_mem_of_fixedPoints _ _ (T131_30 i) (hfix131_30 i) _)
      ⟨131, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T131_30_2 Q2.hfix131_30_2 Q2.hinj131_30_2
      Q2.hcardT131_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_30_2 i) (Q2.hfix131_30_2 i) _)
      colCert_131_30_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T131_30
      hfix131_30 hinj131_30 hcardT131_30
      (fun i => conj_mem_of_fixedPoints _ _ (T131_30 i) (hfix131_30 i) _)
      ⟨131, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T131_30_2 Q2.hfix131_30_2 Q2.hinj131_30_2
      Q2.hcardT131_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_30_2 i) (Q2.hfix131_30_2 i) _)
      colCert_131_30_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T131_30
      hfix131_30 hinj131_30 hcardT131_30
      (fun i => conj_mem_of_fixedPoints _ _ (T131_30 i) (hfix131_30 i) _)
      ⟨131, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T131_30_2 Q2.hfix131_30_2 Q2.hinj131_30_2
      Q2.hcardT131_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_30_2 i) (Q2.hfix131_30_2 i) _)
      colCert_131_30_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T131_30
      hfix131_30 hinj131_30 hcardT131_30
      (fun i => conj_mem_of_fixedPoints _ _ (T131_30 i) (hfix131_30 i) _)
      ⟨131, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T131_30_2 Q2.hfix131_30_2 Q2.hinj131_30_2
      Q2.hcardT131_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_30_2 i) (Q2.hfix131_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T131_30 = colFn colCertDiv_131_30_5.D1 (m := 5) from colCertDiv_131_30_5.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 5 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T131_30_2 = colFn colCertDiv_131_30_5.D2 (m := 5) from colCertDiv_131_30_5.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_30_5_match


theorem leaf_131_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T131_30
      hfix131_30 hinj131_30 hcardT131_30
      (fun i => conj_mem_of_fixedPoints _ _ (T131_30 i) (hfix131_30 i) _)
      ⟨131, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T131_30_2 Q2.hfix131_30_2 Q2.hinj131_30_2
      Q2.hcardT131_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_30_2 i) (Q2.hfix131_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T131_30 = colFn colCertDiv_131_30_10.D1 (m := 5) from colCertDiv_131_30_10.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 10 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T131_30_2 = colFn colCertDiv_131_30_10.D2 (m := 5) from colCertDiv_131_30_10.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_30_10_match


theorem leaf_131_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T131_30
      hfix131_30 hinj131_30 hcardT131_30
      (fun i => conj_mem_of_fixedPoints _ _ (T131_30 i) (hfix131_30 i) _)
      ⟨131, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T131_30_2 Q2.hfix131_30_2 Q2.hinj131_30_2
      Q2.hcardT131_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_30_2 i) (Q2.hfix131_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T131_30 = colFn colCertDiv_131_30_15.D1 (m := 5) from colCertDiv_131_30_15.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 15 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T131_30_2 = colFn colCertDiv_131_30_15.D2 (m := 5) from colCertDiv_131_30_15.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_30_15_match


theorem leaf_131_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T131_30
      hfix131_30 hinj131_30 hcardT131_30
      (fun i => conj_mem_of_fixedPoints _ _ (T131_30 i) (hfix131_30 i) _)
      ⟨131, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T131_30_2 Q2.hfix131_30_2 Q2.hinj131_30_2
      Q2.hcardT131_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_30_2 i) (Q2.hfix131_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T131_30 = colFn colCertDiv_131_30_20.D1 (m := 5) from colCertDiv_131_30_20.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 20 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T131_30_2 = colFn colCertDiv_131_30_20.D2 (m := 5) from colCertDiv_131_30_20.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_30_20_match


theorem leaf_131_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T131_34
      hfix131_34 hinj131_34 hcardT131_34
      (fun i => conj_mem_of_fixedPoints _ _ (T131_34 i) (hfix131_34 i) _)
      ⟨131, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T131_34_2 Q2.hfix131_34_2 Q2.hinj131_34_2
      Q2.hcardT131_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_34_2 i) (Q2.hfix131_34_2 i) _)
      colCert_131_34_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T131_34
      hfix131_34 hinj131_34 hcardT131_34
      (fun i => conj_mem_of_fixedPoints _ _ (T131_34 i) (hfix131_34 i) _)
      ⟨131, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T131_34_2 Q2.hfix131_34_2 Q2.hinj131_34_2
      Q2.hcardT131_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_34_2 i) (Q2.hfix131_34_2 i) _)
      colCert_131_34_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T131_34
      hfix131_34 hinj131_34 hcardT131_34
      (fun i => conj_mem_of_fixedPoints _ _ (T131_34 i) (hfix131_34 i) _)
      ⟨131, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T131_34_2 Q2.hfix131_34_2 Q2.hinj131_34_2
      Q2.hcardT131_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_34_2 i) (Q2.hfix131_34_2 i) _)
      colCert_131_34_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T131_34
      hfix131_34 hinj131_34 hcardT131_34
      (fun i => conj_mem_of_fixedPoints _ _ (T131_34 i) (hfix131_34 i) _)
      ⟨131, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T131_34_2 Q2.hfix131_34_2 Q2.hinj131_34_2
      Q2.hcardT131_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_34_2 i) (Q2.hfix131_34_2 i) _)
      colCert_131_34_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T131_34
      hfix131_34 hinj131_34 hcardT131_34
      (fun i => conj_mem_of_fixedPoints _ _ (T131_34 i) (hfix131_34 i) _)
      ⟨131, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T131_34_2 Q2.hfix131_34_2 Q2.hinj131_34_2
      Q2.hcardT131_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_34_2 i) (Q2.hfix131_34_2 i) _)
      colCert_131_34_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T131_34
      hfix131_34 hinj131_34 hcardT131_34
      (fun i => conj_mem_of_fixedPoints _ _ (T131_34 i) (hfix131_34 i) _)
      ⟨131, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T131_34_2 Q2.hfix131_34_2 Q2.hinj131_34_2
      Q2.hcardT131_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_34_2 i) (Q2.hfix131_34_2 i) _)
      colCert_131_34_5.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T131_34
      hfix131_34 hinj131_34 hcardT131_34
      (fun i => conj_mem_of_fixedPoints _ _ (T131_34 i) (hfix131_34 i) _)
      ⟨131, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T131_34_2 Q2.hfix131_34_2 Q2.hinj131_34_2
      Q2.hcardT131_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_34_2 i) (Q2.hfix131_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T131_34 = colFn colCertDiv_131_34_10.D1 (m := 5) from colCertDiv_131_34_10.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 10 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T131_34_2 = colFn colCertDiv_131_34_10.D2 (m := 5) from colCertDiv_131_34_10.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_34_10_match


theorem leaf_131_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T131_34
      hfix131_34 hinj131_34 hcardT131_34
      (fun i => conj_mem_of_fixedPoints _ _ (T131_34 i) (hfix131_34 i) _)
      ⟨131, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T131_34_2 Q2.hfix131_34_2 Q2.hinj131_34_2
      Q2.hcardT131_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_34_2 i) (Q2.hfix131_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T131_34 = colFn colCertDiv_131_34_15.D1 (m := 5) from colCertDiv_131_34_15.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 15 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T131_34_2 = colFn colCertDiv_131_34_15.D2 (m := 5) from colCertDiv_131_34_15.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_34_15_match


theorem leaf_131_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T131_34
      hfix131_34 hinj131_34 hcardT131_34
      (fun i => conj_mem_of_fixedPoints _ _ (T131_34 i) (hfix131_34 i) _)
      ⟨131, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T131_34_2 Q2.hfix131_34_2 Q2.hinj131_34_2
      Q2.hcardT131_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_34_2 i) (Q2.hfix131_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T131_34 = colFn colCertDiv_131_34_20.D1 (m := 5) from colCertDiv_131_34_20.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 20 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T131_34_2 = colFn colCertDiv_131_34_20.D2 (m := 5) from colCertDiv_131_34_20.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_34_20_match


theorem leaf_131_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T131_42
      hfix131_42 hinj131_42 hcardT131_42
      (fun i => conj_mem_of_fixedPoints _ _ (T131_42 i) (hfix131_42 i) _)
      ⟨131, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T131_42_2 Q2.hfix131_42_2 Q2.hinj131_42_2
      Q2.hcardT131_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_42_2 i) (Q2.hfix131_42_2 i) _)
      colCert_131_42_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T131_42
      hfix131_42 hinj131_42 hcardT131_42
      (fun i => conj_mem_of_fixedPoints _ _ (T131_42 i) (hfix131_42 i) _)
      ⟨131, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T131_42_2 Q2.hfix131_42_2 Q2.hinj131_42_2
      Q2.hcardT131_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_42_2 i) (Q2.hfix131_42_2 i) _)
      colCert_131_42_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T131_42
      hfix131_42 hinj131_42 hcardT131_42
      (fun i => conj_mem_of_fixedPoints _ _ (T131_42 i) (hfix131_42 i) _)
      ⟨131, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T131_42_2 Q2.hfix131_42_2 Q2.hinj131_42_2
      Q2.hcardT131_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_42_2 i) (Q2.hfix131_42_2 i) _)
      colCert_131_42_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T131_42
      hfix131_42 hinj131_42 hcardT131_42
      (fun i => conj_mem_of_fixedPoints _ _ (T131_42 i) (hfix131_42 i) _)
      ⟨131, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T131_42_2 Q2.hfix131_42_2 Q2.hinj131_42_2
      Q2.hcardT131_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_42_2 i) (Q2.hfix131_42_2 i) _)
      colCert_131_42_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T131_42
      hfix131_42 hinj131_42 hcardT131_42
      (fun i => conj_mem_of_fixedPoints _ _ (T131_42 i) (hfix131_42 i) _)
      ⟨131, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T131_42_2 Q2.hfix131_42_2 Q2.hinj131_42_2
      Q2.hcardT131_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_42_2 i) (Q2.hfix131_42_2 i) _)
      colCert_131_42_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T131_42
      hfix131_42 hinj131_42 hcardT131_42
      (fun i => conj_mem_of_fixedPoints _ _ (T131_42 i) (hfix131_42 i) _)
      ⟨131, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T131_42_2 Q2.hfix131_42_2 Q2.hinj131_42_2
      Q2.hcardT131_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_42_2 i) (Q2.hfix131_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T131_42 = colFn colCertDiv_131_42_5.D1 (m := 5) from colCertDiv_131_42_5.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T131_42_2 = colFn colCertDiv_131_42_5.D2 (m := 5) from colCertDiv_131_42_5.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_42_5_match


theorem leaf_131_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T131_42
      hfix131_42 hinj131_42 hcardT131_42
      (fun i => conj_mem_of_fixedPoints _ _ (T131_42 i) (hfix131_42 i) _)
      ⟨131, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T131_42_2 Q2.hfix131_42_2 Q2.hinj131_42_2
      Q2.hcardT131_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_42_2 i) (Q2.hfix131_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T131_42 = colFn colCertDiv_131_42_10.D1 (m := 5) from colCertDiv_131_42_10.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T131_42_2 = colFn colCertDiv_131_42_10.D2 (m := 5) from colCertDiv_131_42_10.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_42_10_match


theorem leaf_131_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T131_42
      hfix131_42 hinj131_42 hcardT131_42
      (fun i => conj_mem_of_fixedPoints _ _ (T131_42 i) (hfix131_42 i) _)
      ⟨131, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T131_42_2 Q2.hfix131_42_2 Q2.hinj131_42_2
      Q2.hcardT131_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_42_2 i) (Q2.hfix131_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T131_42 = colFn colCertDiv_131_42_15.D1 (m := 5) from colCertDiv_131_42_15.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T131_42_2 = colFn colCertDiv_131_42_15.D2 (m := 5) from colCertDiv_131_42_15.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_42_15_match


theorem leaf_131_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T131_42
      hfix131_42 hinj131_42 hcardT131_42
      (fun i => conj_mem_of_fixedPoints _ _ (T131_42 i) (hfix131_42 i) _)
      ⟨131, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T131_42_2 Q2.hfix131_42_2 Q2.hinj131_42_2
      Q2.hcardT131_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_42_2 i) (Q2.hfix131_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T131_42 = colFn colCertDiv_131_42_20.D1 (m := 5) from colCertDiv_131_42_20.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T131_42_2 = colFn colCertDiv_131_42_20.D2 (m := 5) from colCertDiv_131_42_20.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_42_20_match


theorem leaf_131_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T131_46
      hfix131_46 hinj131_46 hcardT131_46
      (fun i => conj_mem_of_fixedPoints _ _ (T131_46 i) (hfix131_46 i) _)
      ⟨131, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T131_46_2 Q2.hfix131_46_2 Q2.hinj131_46_2
      Q2.hcardT131_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_46_2 i) (Q2.hfix131_46_2 i) _)
      colCert_131_46_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T131_46
      hfix131_46 hinj131_46 hcardT131_46
      (fun i => conj_mem_of_fixedPoints _ _ (T131_46 i) (hfix131_46 i) _)
      ⟨131, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T131_46_2 Q2.hfix131_46_2 Q2.hinj131_46_2
      Q2.hcardT131_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_46_2 i) (Q2.hfix131_46_2 i) _)
      colCert_131_46_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T131_46
      hfix131_46 hinj131_46 hcardT131_46
      (fun i => conj_mem_of_fixedPoints _ _ (T131_46 i) (hfix131_46 i) _)
      ⟨131, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T131_46_2 Q2.hfix131_46_2 Q2.hinj131_46_2
      Q2.hcardT131_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_46_2 i) (Q2.hfix131_46_2 i) _)
      colCert_131_46_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T131_46
      hfix131_46 hinj131_46 hcardT131_46
      (fun i => conj_mem_of_fixedPoints _ _ (T131_46 i) (hfix131_46 i) _)
      ⟨131, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T131_46_2 Q2.hfix131_46_2 Q2.hinj131_46_2
      Q2.hcardT131_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_46_2 i) (Q2.hfix131_46_2 i) _)
      colCert_131_46_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T131_46
      hfix131_46 hinj131_46 hcardT131_46
      (fun i => conj_mem_of_fixedPoints _ _ (T131_46 i) (hfix131_46 i) _)
      ⟨131, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T131_46_2 Q2.hfix131_46_2 Q2.hinj131_46_2
      Q2.hcardT131_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_46_2 i) (Q2.hfix131_46_2 i) _)
      colCert_131_46_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T131_46
      hfix131_46 hinj131_46 hcardT131_46
      (fun i => conj_mem_of_fixedPoints _ _ (T131_46 i) (hfix131_46 i) _)
      ⟨131, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T131_46_2 Q2.hfix131_46_2 Q2.hinj131_46_2
      Q2.hcardT131_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_46_2 i) (Q2.hfix131_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T131_46 = colFn colCertDiv_131_46_5.D1 (m := 5) from colCertDiv_131_46_5.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 5 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T131_46_2 = colFn colCertDiv_131_46_5.D2 (m := 5) from colCertDiv_131_46_5.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_46_5_match


theorem leaf_131_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T131_46
      hfix131_46 hinj131_46 hcardT131_46
      (fun i => conj_mem_of_fixedPoints _ _ (T131_46 i) (hfix131_46 i) _)
      ⟨131, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T131_46_2 Q2.hfix131_46_2 Q2.hinj131_46_2
      Q2.hcardT131_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_46_2 i) (Q2.hfix131_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T131_46 = colFn colCertDiv_131_46_10.D1 (m := 5) from colCertDiv_131_46_10.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 10 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T131_46_2 = colFn colCertDiv_131_46_10.D2 (m := 5) from colCertDiv_131_46_10.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_46_10_match


theorem leaf_131_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T131_46
      hfix131_46 hinj131_46 hcardT131_46
      (fun i => conj_mem_of_fixedPoints _ _ (T131_46 i) (hfix131_46 i) _)
      ⟨131, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T131_46_2 Q2.hfix131_46_2 Q2.hinj131_46_2
      Q2.hcardT131_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_46_2 i) (Q2.hfix131_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T131_46 = colFn colCertDiv_131_46_15.D1 (m := 5) from colCertDiv_131_46_15.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 15 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T131_46_2 = colFn colCertDiv_131_46_15.D2 (m := 5) from colCertDiv_131_46_15.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_46_15_match


theorem leaf_131_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T131_46
      hfix131_46 hinj131_46 hcardT131_46
      (fun i => conj_mem_of_fixedPoints _ _ (T131_46 i) (hfix131_46 i) _)
      ⟨131, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T131_46_2 Q2.hfix131_46_2 Q2.hinj131_46_2
      Q2.hcardT131_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_46_2 i) (Q2.hfix131_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T131_46 = colFn colCertDiv_131_46_20.D1 (m := 5) from colCertDiv_131_46_20.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 20 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T131_46_2 = colFn colCertDiv_131_46_20.D2 (m := 5) from colCertDiv_131_46_20.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_46_20_match


theorem leaf_131_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T131_48
      hfix131_48 hinj131_48 hcardT131_48
      (fun i => conj_mem_of_fixedPoints _ _ (T131_48 i) (hfix131_48 i) _)
      ⟨131, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T131_48_2 Q2.hfix131_48_2 Q2.hinj131_48_2
      Q2.hcardT131_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_48_2 i) (Q2.hfix131_48_2 i) _)
      colCert_131_48_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T131_48
      hfix131_48 hinj131_48 hcardT131_48
      (fun i => conj_mem_of_fixedPoints _ _ (T131_48 i) (hfix131_48 i) _)
      ⟨131, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T131_48_2 Q2.hfix131_48_2 Q2.hinj131_48_2
      Q2.hcardT131_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_48_2 i) (Q2.hfix131_48_2 i) _)
      colCert_131_48_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T131_48
      hfix131_48 hinj131_48 hcardT131_48
      (fun i => conj_mem_of_fixedPoints _ _ (T131_48 i) (hfix131_48 i) _)
      ⟨131, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T131_48_2 Q2.hfix131_48_2 Q2.hinj131_48_2
      Q2.hcardT131_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_48_2 i) (Q2.hfix131_48_2 i) _)
      colCert_131_48_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T131_48
      hfix131_48 hinj131_48 hcardT131_48
      (fun i => conj_mem_of_fixedPoints _ _ (T131_48 i) (hfix131_48 i) _)
      ⟨131, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T131_48_2 Q2.hfix131_48_2 Q2.hinj131_48_2
      Q2.hcardT131_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_48_2 i) (Q2.hfix131_48_2 i) _)
      colCert_131_48_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T131_48
      hfix131_48 hinj131_48 hcardT131_48
      (fun i => conj_mem_of_fixedPoints _ _ (T131_48 i) (hfix131_48 i) _)
      ⟨131, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T131_48_2 Q2.hfix131_48_2 Q2.hinj131_48_2
      Q2.hcardT131_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_48_2 i) (Q2.hfix131_48_2 i) _)
      colCert_131_48_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T131_48
      hfix131_48 hinj131_48 hcardT131_48
      (fun i => conj_mem_of_fixedPoints _ _ (T131_48 i) (hfix131_48 i) _)
      ⟨131, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T131_48_2 Q2.hfix131_48_2 Q2.hinj131_48_2
      Q2.hcardT131_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_48_2 i) (Q2.hfix131_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T131_48 = colFn colCertDiv_131_48_5.D1 (m := 5) from colCertDiv_131_48_5.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T131_48_2 = colFn colCertDiv_131_48_5.D2 (m := 5) from colCertDiv_131_48_5.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_48_5_match


theorem leaf_131_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T131_48
      hfix131_48 hinj131_48 hcardT131_48
      (fun i => conj_mem_of_fixedPoints _ _ (T131_48 i) (hfix131_48 i) _)
      ⟨131, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T131_48_2 Q2.hfix131_48_2 Q2.hinj131_48_2
      Q2.hcardT131_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_48_2 i) (Q2.hfix131_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T131_48 = colFn colCertDiv_131_48_10.D1 (m := 5) from colCertDiv_131_48_10.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T131_48_2 = colFn colCertDiv_131_48_10.D2 (m := 5) from colCertDiv_131_48_10.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_48_10_match


theorem leaf_131_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T131_48
      hfix131_48 hinj131_48 hcardT131_48
      (fun i => conj_mem_of_fixedPoints _ _ (T131_48 i) (hfix131_48 i) _)
      ⟨131, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T131_48_2 Q2.hfix131_48_2 Q2.hinj131_48_2
      Q2.hcardT131_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_48_2 i) (Q2.hfix131_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T131_48 = colFn colCertDiv_131_48_15.D1 (m := 5) from colCertDiv_131_48_15.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T131_48_2 = colFn colCertDiv_131_48_15.D2 (m := 5) from colCertDiv_131_48_15.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_48_15_match


theorem leaf_131_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T131_48
      hfix131_48 hinj131_48 hcardT131_48
      (fun i => conj_mem_of_fixedPoints _ _ (T131_48 i) (hfix131_48 i) _)
      ⟨131, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T131_48_2 Q2.hfix131_48_2 Q2.hinj131_48_2
      Q2.hcardT131_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_48_2 i) (Q2.hfix131_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T131_48 = colFn colCertDiv_131_48_20.D1 (m := 5) from colCertDiv_131_48_20.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T131_48_2 = colFn colCertDiv_131_48_20.D2 (m := 5) from colCertDiv_131_48_20.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_48_20_match


theorem leaf_131_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T131_53
      hfix131_53 hinj131_53 hcardT131_53
      (fun i => conj_mem_of_fixedPoints _ _ (T131_53 i) (hfix131_53 i) _)
      ⟨131, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T131_53_2 Q2.hfix131_53_2 Q2.hinj131_53_2
      Q2.hcardT131_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_53_2 i) (Q2.hfix131_53_2 i) _)
      colCert_131_53_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T131_53
      hfix131_53 hinj131_53 hcardT131_53
      (fun i => conj_mem_of_fixedPoints _ _ (T131_53 i) (hfix131_53 i) _)
      ⟨131, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T131_53_2 Q2.hfix131_53_2 Q2.hinj131_53_2
      Q2.hcardT131_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_53_2 i) (Q2.hfix131_53_2 i) _)
      colCert_131_53_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T131_53
      hfix131_53 hinj131_53 hcardT131_53
      (fun i => conj_mem_of_fixedPoints _ _ (T131_53 i) (hfix131_53 i) _)
      ⟨131, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T131_53_2 Q2.hfix131_53_2 Q2.hinj131_53_2
      Q2.hcardT131_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_53_2 i) (Q2.hfix131_53_2 i) _)
      colCert_131_53_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T131_53
      hfix131_53 hinj131_53 hcardT131_53
      (fun i => conj_mem_of_fixedPoints _ _ (T131_53 i) (hfix131_53 i) _)
      ⟨131, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T131_53_2 Q2.hfix131_53_2 Q2.hinj131_53_2
      Q2.hcardT131_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_53_2 i) (Q2.hfix131_53_2 i) _)
      colCert_131_53_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T131_53
      hfix131_53 hinj131_53 hcardT131_53
      (fun i => conj_mem_of_fixedPoints _ _ (T131_53 i) (hfix131_53 i) _)
      ⟨131, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T131_53_2 Q2.hfix131_53_2 Q2.hinj131_53_2
      Q2.hcardT131_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_53_2 i) (Q2.hfix131_53_2 i) _)
      colCert_131_53_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T131_53
      hfix131_53 hinj131_53 hcardT131_53
      (fun i => conj_mem_of_fixedPoints _ _ (T131_53 i) (hfix131_53 i) _)
      ⟨131, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T131_53_2 Q2.hfix131_53_2 Q2.hinj131_53_2
      Q2.hcardT131_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_53_2 i) (Q2.hfix131_53_2 i) _)
      colCert_131_53_5.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T131_53
      hfix131_53 hinj131_53 hcardT131_53
      (fun i => conj_mem_of_fixedPoints _ _ (T131_53 i) (hfix131_53 i) _)
      ⟨131, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T131_53_2 Q2.hfix131_53_2 Q2.hinj131_53_2
      Q2.hcardT131_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_53_2 i) (Q2.hfix131_53_2 i) _)
      colCert_131_53_10.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T131_53
      hfix131_53 hinj131_53 hcardT131_53
      (fun i => conj_mem_of_fixedPoints _ _ (T131_53 i) (hfix131_53 i) _)
      ⟨131, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T131_53_2 Q2.hfix131_53_2 Q2.hinj131_53_2
      Q2.hcardT131_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_53_2 i) (Q2.hfix131_53_2 i) _)
      colCert_131_53_15.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T131_53
      hfix131_53 hinj131_53 hcardT131_53
      (fun i => conj_mem_of_fixedPoints _ _ (T131_53 i) (hfix131_53 i) _)
      ⟨131, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T131_53_2 Q2.hfix131_53_2 Q2.hinj131_53_2
      Q2.hcardT131_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_53_2 i) (Q2.hfix131_53_2 i) _)
      colCert_131_53_20.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_83_0 (hp : 0 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp)) T131_83
      hfix131_83 hinj131_83 hcardT131_83
      (fun i => conj_mem_of_fixedPoints _ _ (T131_83 i) (hfix131_83 i) _)
      ⟨131, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 0 hp) Q2.T131_83_2 Q2.hfix131_83_2 Q2.hinj131_83_2
      Q2.hcardT131_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_83_2 i) (Q2.hfix131_83_2 i) _)
      colCert_131_83_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_83_1 (hp : 1 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp)) T131_83
      hfix131_83 hinj131_83 hcardT131_83
      (fun i => conj_mem_of_fixedPoints _ _ (T131_83 i) (hfix131_83 i) _)
      ⟨131, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 1 hp) Q2.T131_83_2 Q2.hfix131_83_2 Q2.hinj131_83_2
      Q2.hcardT131_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_83_2 i) (Q2.hfix131_83_2 i) _)
      colCert_131_83_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_83_2 (hp : 2 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp)) T131_83
      hfix131_83 hinj131_83 hcardT131_83
      (fun i => conj_mem_of_fixedPoints _ _ (T131_83 i) (hfix131_83 i) _)
      ⟨131, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 2 hp) Q2.T131_83_2 Q2.hfix131_83_2 Q2.hinj131_83_2
      Q2.hcardT131_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_83_2 i) (Q2.hfix131_83_2 i) _)
      colCert_131_83_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_83_3 (hp : 3 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp)) T131_83
      hfix131_83 hinj131_83 hcardT131_83
      (fun i => conj_mem_of_fixedPoints _ _ (T131_83 i) (hfix131_83 i) _)
      ⟨131, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 3 hp) Q2.T131_83_2 Q2.hfix131_83_2 Q2.hinj131_83_2
      Q2.hcardT131_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_83_2 i) (Q2.hfix131_83_2 i) _)
      colCert_131_83_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_83_4 (hp : 4 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp)) T131_83
      hfix131_83 hinj131_83 hcardT131_83
      (fun i => conj_mem_of_fixedPoints _ _ (T131_83 i) (hfix131_83 i) _)
      ⟨131, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 4 hp) Q2.T131_83_2 Q2.hfix131_83_2 Q2.hinj131_83_2
      Q2.hcardT131_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_83_2 i) (Q2.hfix131_83_2 i) _)
      colCert_131_83_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_83_5 (hp : 5 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp)) T131_83
      hfix131_83 hinj131_83 hcardT131_83
      (fun i => conj_mem_of_fixedPoints _ _ (T131_83 i) (hfix131_83 i) _)
      ⟨131, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 5 hp) Q2.T131_83_2 Q2.hfix131_83_2 Q2.hinj131_83_2
      Q2.hcardT131_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_83_2 i) (Q2.hfix131_83_2 i) _)
      colCert_131_83_5.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_83_10 (hp : 10 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp)) T131_83
      hfix131_83 hinj131_83 hcardT131_83
      (fun i => conj_mem_of_fixedPoints _ _ (T131_83 i) (hfix131_83 i) _)
      ⟨131, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 10 hp) Q2.T131_83_2 Q2.hfix131_83_2 Q2.hinj131_83_2
      Q2.hcardT131_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_83_2 i) (Q2.hfix131_83_2 i) _)
      colCert_131_83_10.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_83_15 (hp : 15 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp)) T131_83
      hfix131_83 hinj131_83 hcardT131_83
      (fun i => conj_mem_of_fixedPoints _ _ (T131_83 i) (hfix131_83 i) _)
      ⟨131, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 15 hp) Q2.T131_83_2 Q2.hfix131_83_2 Q2.hinj131_83_2
      Q2.hcardT131_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_83_2 i) (Q2.hfix131_83_2 i) _)
      colCert_131_83_15.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_83_20 (hp : 20 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp)) T131_83
      hfix131_83 hinj131_83 hcardT131_83
      (fun i => conj_mem_of_fixedPoints _ _ (T131_83 i) (hfix131_83 i) _)
      ⟨131, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 20 hp) Q2.T131_83_2 Q2.hfix131_83_2 Q2.hinj131_83_2
      Q2.hcardT131_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_83_2 i) (Q2.hfix131_83_2 i) _)
      colCert_131_83_20.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_92_0 (hp : 0 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp)) T131_92
      hfix131_92 hinj131_92 hcardT131_92
      (fun i => conj_mem_of_fixedPoints _ _ (T131_92 i) (hfix131_92 i) _)
      ⟨131, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 0 hp) Q2.T131_92_2 Q2.hfix131_92_2 Q2.hinj131_92_2
      Q2.hcardT131_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_92_2 i) (Q2.hfix131_92_2 i) _)
      colCert_131_92_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_92_1 (hp : 1 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp)) T131_92
      hfix131_92 hinj131_92 hcardT131_92
      (fun i => conj_mem_of_fixedPoints _ _ (T131_92 i) (hfix131_92 i) _)
      ⟨131, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 1 hp) Q2.T131_92_2 Q2.hfix131_92_2 Q2.hinj131_92_2
      Q2.hcardT131_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_92_2 i) (Q2.hfix131_92_2 i) _)
      colCert_131_92_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_92_2 (hp : 2 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp)) T131_92
      hfix131_92 hinj131_92 hcardT131_92
      (fun i => conj_mem_of_fixedPoints _ _ (T131_92 i) (hfix131_92 i) _)
      ⟨131, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 2 hp) Q2.T131_92_2 Q2.hfix131_92_2 Q2.hinj131_92_2
      Q2.hcardT131_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_92_2 i) (Q2.hfix131_92_2 i) _)
      colCert_131_92_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_92_3 (hp : 3 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp)) T131_92
      hfix131_92 hinj131_92 hcardT131_92
      (fun i => conj_mem_of_fixedPoints _ _ (T131_92 i) (hfix131_92 i) _)
      ⟨131, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 3 hp) Q2.T131_92_2 Q2.hfix131_92_2 Q2.hinj131_92_2
      Q2.hcardT131_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_92_2 i) (Q2.hfix131_92_2 i) _)
      colCert_131_92_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_92_4 (hp : 4 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp)) T131_92
      hfix131_92 hinj131_92 hcardT131_92
      (fun i => conj_mem_of_fixedPoints _ _ (T131_92 i) (hfix131_92 i) _)
      ⟨131, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 4 hp) Q2.T131_92_2 Q2.hfix131_92_2 Q2.hinj131_92_2
      Q2.hcardT131_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_92_2 i) (Q2.hfix131_92_2 i) _)
      colCert_131_92_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_92_5 (hp : 5 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp)) T131_92
      hfix131_92 hinj131_92 hcardT131_92
      (fun i => conj_mem_of_fixedPoints _ _ (T131_92 i) (hfix131_92 i) _)
      ⟨131, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 5 hp) Q2.T131_92_2 Q2.hfix131_92_2 Q2.hinj131_92_2
      Q2.hcardT131_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_92_2 i) (Q2.hfix131_92_2 i) _)
      colCert_131_92_5.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_92_10 (hp : 10 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp)) T131_92
      hfix131_92 hinj131_92 hcardT131_92
      (fun i => conj_mem_of_fixedPoints _ _ (T131_92 i) (hfix131_92 i) _)
      ⟨131, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 10 hp) Q2.T131_92_2 Q2.hfix131_92_2 Q2.hinj131_92_2
      Q2.hcardT131_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_92_2 i) (Q2.hfix131_92_2 i) _)
      colCert_131_92_10.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_92_15 (hp : 15 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp)) T131_92
      hfix131_92 hinj131_92 hcardT131_92
      (fun i => conj_mem_of_fixedPoints _ _ (T131_92 i) (hfix131_92 i) _)
      ⟨131, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 15 hp) Q2.T131_92_2 Q2.hfix131_92_2 Q2.hinj131_92_2
      Q2.hcardT131_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_92_2 i) (Q2.hfix131_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T131_92 = colFn colCertDiv_131_92_15.D1 (m := 5) from colCertDiv_131_92_15.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 15 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T131_92_2 = colFn colCertDiv_131_92_15.D2 (m := 5) from colCertDiv_131_92_15.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_92_15_match


theorem leaf_131_92_20 (hp : 20 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp)) T131_92
      hfix131_92 hinj131_92 hcardT131_92
      (fun i => conj_mem_of_fixedPoints _ _ (T131_92 i) (hfix131_92 i) _)
      ⟨131, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 20 hp) Q2.T131_92_2 Q2.hfix131_92_2 Q2.hinj131_92_2
      Q2.hcardT131_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_92_2 i) (Q2.hfix131_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T131_92 = colFn colCertDiv_131_92_20.D1 (m := 5) from colCertDiv_131_92_20.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 20 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T131_92_2 = colFn colCertDiv_131_92_20.D2 (m := 5) from colCertDiv_131_92_20.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_92_20_match


theorem leaf_131_96_0 (hp : 0 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp)) T131_96
      hfix131_96 hinj131_96 hcardT131_96
      (fun i => conj_mem_of_fixedPoints _ _ (T131_96 i) (hfix131_96 i) _)
      ⟨131, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 0 hp) Q2.T131_96_2 Q2.hfix131_96_2 Q2.hinj131_96_2
      Q2.hcardT131_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_96_2 i) (Q2.hfix131_96_2 i) _)
      colCert_131_96_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_96_1 (hp : 1 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp)) T131_96
      hfix131_96 hinj131_96 hcardT131_96
      (fun i => conj_mem_of_fixedPoints _ _ (T131_96 i) (hfix131_96 i) _)
      ⟨131, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 1 hp) Q2.T131_96_2 Q2.hfix131_96_2 Q2.hinj131_96_2
      Q2.hcardT131_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_96_2 i) (Q2.hfix131_96_2 i) _)
      colCert_131_96_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_96_2 (hp : 2 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp)) T131_96
      hfix131_96 hinj131_96 hcardT131_96
      (fun i => conj_mem_of_fixedPoints _ _ (T131_96 i) (hfix131_96 i) _)
      ⟨131, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 2 hp) Q2.T131_96_2 Q2.hfix131_96_2 Q2.hinj131_96_2
      Q2.hcardT131_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_96_2 i) (Q2.hfix131_96_2 i) _)
      colCert_131_96_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_96_3 (hp : 3 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp)) T131_96
      hfix131_96 hinj131_96 hcardT131_96
      (fun i => conj_mem_of_fixedPoints _ _ (T131_96 i) (hfix131_96 i) _)
      ⟨131, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 3 hp) Q2.T131_96_2 Q2.hfix131_96_2 Q2.hinj131_96_2
      Q2.hcardT131_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_96_2 i) (Q2.hfix131_96_2 i) _)
      colCert_131_96_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_96_4 (hp : 4 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp)) T131_96
      hfix131_96 hinj131_96 hcardT131_96
      (fun i => conj_mem_of_fixedPoints _ _ (T131_96 i) (hfix131_96 i) _)
      ⟨131, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 4 hp) Q2.T131_96_2 Q2.hfix131_96_2 Q2.hinj131_96_2
      Q2.hcardT131_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_96_2 i) (Q2.hfix131_96_2 i) _)
      colCert_131_96_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_96_5 (hp : 5 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp)) T131_96
      hfix131_96 hinj131_96 hcardT131_96
      (fun i => conj_mem_of_fixedPoints _ _ (T131_96 i) (hfix131_96 i) _)
      ⟨131, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 5 hp) Q2.T131_96_2 Q2.hfix131_96_2 Q2.hinj131_96_2
      Q2.hcardT131_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_96_2 i) (Q2.hfix131_96_2 i) _)
      colCert_131_96_5.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_96_10 (hp : 10 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp)) T131_96
      hfix131_96 hinj131_96 hcardT131_96
      (fun i => conj_mem_of_fixedPoints _ _ (T131_96 i) (hfix131_96 i) _)
      ⟨131, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 10 hp) Q2.T131_96_2 Q2.hfix131_96_2 Q2.hinj131_96_2
      Q2.hcardT131_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_96_2 i) (Q2.hfix131_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T131_96 = colFn colCertDiv_131_96_10.D1 (m := 5) from colCertDiv_131_96_10.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 10 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T131_96_2 = colFn colCertDiv_131_96_10.D2 (m := 5) from colCertDiv_131_96_10.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_96_10_match


theorem leaf_131_96_15 (hp : 15 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp)) T131_96
      hfix131_96 hinj131_96 hcardT131_96
      (fun i => conj_mem_of_fixedPoints _ _ (T131_96 i) (hfix131_96 i) _)
      ⟨131, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 15 hp) Q2.T131_96_2 Q2.hfix131_96_2 Q2.hinj131_96_2
      Q2.hcardT131_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_96_2 i) (Q2.hfix131_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T131_96 = colFn colCertDiv_131_96_15.D1 (m := 5) from colCertDiv_131_96_15.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 15 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T131_96_2 = colFn colCertDiv_131_96_15.D2 (m := 5) from colCertDiv_131_96_15.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_96_15_match


theorem leaf_131_96_20 (hp : 20 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp)) T131_96
      hfix131_96 hinj131_96 hcardT131_96
      (fun i => conj_mem_of_fixedPoints _ _ (T131_96 i) (hfix131_96 i) _)
      ⟨131, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 20 hp) Q2.T131_96_2 Q2.hfix131_96_2 Q2.hinj131_96_2
      Q2.hcardT131_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_96_2 i) (Q2.hfix131_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T131_96 = colFn colCertDiv_131_96_20.D1 (m := 5) from colCertDiv_131_96_20.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 20 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T131_96_2 = colFn colCertDiv_131_96_20.D2 (m := 5) from colCertDiv_131_96_20.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_96_20_match


theorem leaf_131_104_0 (hp : 0 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp)) T131_104
      hfix131_104 hinj131_104 hcardT131_104
      (fun i => conj_mem_of_fixedPoints _ _ (T131_104 i) (hfix131_104 i) _)
      ⟨131, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 0 hp) Q2.T131_104_2 Q2.hfix131_104_2 Q2.hinj131_104_2
      Q2.hcardT131_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_104_2 i) (Q2.hfix131_104_2 i) _)
      colCert_131_104_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_104_1 (hp : 1 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp)) T131_104
      hfix131_104 hinj131_104 hcardT131_104
      (fun i => conj_mem_of_fixedPoints _ _ (T131_104 i) (hfix131_104 i) _)
      ⟨131, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 1 hp) Q2.T131_104_2 Q2.hfix131_104_2 Q2.hinj131_104_2
      Q2.hcardT131_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_104_2 i) (Q2.hfix131_104_2 i) _)
      colCert_131_104_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_104_2 (hp : 2 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp)) T131_104
      hfix131_104 hinj131_104 hcardT131_104
      (fun i => conj_mem_of_fixedPoints _ _ (T131_104 i) (hfix131_104 i) _)
      ⟨131, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 2 hp) Q2.T131_104_2 Q2.hfix131_104_2 Q2.hinj131_104_2
      Q2.hcardT131_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_104_2 i) (Q2.hfix131_104_2 i) _)
      colCert_131_104_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_104_3 (hp : 3 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp)) T131_104
      hfix131_104 hinj131_104 hcardT131_104
      (fun i => conj_mem_of_fixedPoints _ _ (T131_104 i) (hfix131_104 i) _)
      ⟨131, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 3 hp) Q2.T131_104_2 Q2.hfix131_104_2 Q2.hinj131_104_2
      Q2.hcardT131_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_104_2 i) (Q2.hfix131_104_2 i) _)
      colCert_131_104_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_104_4 (hp : 4 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp)) T131_104
      hfix131_104 hinj131_104 hcardT131_104
      (fun i => conj_mem_of_fixedPoints _ _ (T131_104 i) (hfix131_104 i) _)
      ⟨131, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 4 hp) Q2.T131_104_2 Q2.hfix131_104_2 Q2.hinj131_104_2
      Q2.hcardT131_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_104_2 i) (Q2.hfix131_104_2 i) _)
      colCert_131_104_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_104_5 (hp : 5 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp)) T131_104
      hfix131_104 hinj131_104 hcardT131_104
      (fun i => conj_mem_of_fixedPoints _ _ (T131_104 i) (hfix131_104 i) _)
      ⟨131, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 5 hp) Q2.T131_104_2 Q2.hfix131_104_2 Q2.hinj131_104_2
      Q2.hcardT131_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_104_2 i) (Q2.hfix131_104_2 i) _)
      colCert_131_104_5.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_104_10 (hp : 10 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp)) T131_104
      hfix131_104 hinj131_104 hcardT131_104
      (fun i => conj_mem_of_fixedPoints _ _ (T131_104 i) (hfix131_104 i) _)
      ⟨131, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 10 hp) Q2.T131_104_2 Q2.hfix131_104_2 Q2.hinj131_104_2
      Q2.hcardT131_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_104_2 i) (Q2.hfix131_104_2 i) _)
      colCert_131_104_10.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_104_15 (hp : 15 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp)) T131_104
      hfix131_104 hinj131_104 hcardT131_104
      (fun i => conj_mem_of_fixedPoints _ _ (T131_104 i) (hfix131_104 i) _)
      ⟨131, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 15 hp) Q2.T131_104_2 Q2.hfix131_104_2 Q2.hinj131_104_2
      Q2.hcardT131_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_104_2 i) (Q2.hfix131_104_2 i) _)
      colCert_131_104_15.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_104_20 (hp : 20 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp)) T131_104
      hfix131_104 hinj131_104 hcardT131_104
      (fun i => conj_mem_of_fixedPoints _ _ (T131_104 i) (hfix131_104 i) _)
      ⟨131, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 20 hp) Q2.T131_104_2 Q2.hfix131_104_2 Q2.hinj131_104_2
      Q2.hcardT131_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_104_2 i) (Q2.hfix131_104_2 i) _)
      colCert_131_104_20.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_108_0 (hp : 0 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 0 (transLenTr ⟨108, by decide⟩ 0 hp)) T131_108
      hfix131_108 hinj131_108 hcardT131_108
      (fun i => conj_mem_of_fixedPoints _ _ (T131_108 i) (hfix131_108 i) _)
      ⟨131, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 0 hp) Q2.T131_108_2 Q2.hfix131_108_2 Q2.hinj131_108_2
      Q2.hcardT131_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_108_2 i) (Q2.hfix131_108_2 i) _)
      colCert_131_108_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_108_1 (hp : 1 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 1 (transLenTr ⟨108, by decide⟩ 1 hp)) T131_108
      hfix131_108 hinj131_108 hcardT131_108
      (fun i => conj_mem_of_fixedPoints _ _ (T131_108 i) (hfix131_108 i) _)
      ⟨131, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 1 hp) Q2.T131_108_2 Q2.hfix131_108_2 Q2.hinj131_108_2
      Q2.hcardT131_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_108_2 i) (Q2.hfix131_108_2 i) _)
      colCert_131_108_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_108_2 (hp : 2 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 2 (transLenTr ⟨108, by decide⟩ 2 hp)) T131_108
      hfix131_108 hinj131_108 hcardT131_108
      (fun i => conj_mem_of_fixedPoints _ _ (T131_108 i) (hfix131_108 i) _)
      ⟨131, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 2 hp) Q2.T131_108_2 Q2.hfix131_108_2 Q2.hinj131_108_2
      Q2.hcardT131_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_108_2 i) (Q2.hfix131_108_2 i) _)
      colCert_131_108_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_108_3 (hp : 3 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 3 (transLenTr ⟨108, by decide⟩ 3 hp)) T131_108
      hfix131_108 hinj131_108 hcardT131_108
      (fun i => conj_mem_of_fixedPoints _ _ (T131_108 i) (hfix131_108 i) _)
      ⟨131, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 3 hp) Q2.T131_108_2 Q2.hfix131_108_2 Q2.hinj131_108_2
      Q2.hcardT131_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_108_2 i) (Q2.hfix131_108_2 i) _)
      colCert_131_108_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_108_4 (hp : 4 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 4 (transLenTr ⟨108, by decide⟩ 4 hp)) T131_108
      hfix131_108 hinj131_108 hcardT131_108
      (fun i => conj_mem_of_fixedPoints _ _ (T131_108 i) (hfix131_108 i) _)
      ⟨131, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 4 hp) Q2.T131_108_2 Q2.hfix131_108_2 Q2.hinj131_108_2
      Q2.hcardT131_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_108_2 i) (Q2.hfix131_108_2 i) _)
      colCert_131_108_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_108_5 (hp : 5 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 5 (transLenTr ⟨108, by decide⟩ 5 hp)) T131_108
      hfix131_108 hinj131_108 hcardT131_108
      (fun i => conj_mem_of_fixedPoints _ _ (T131_108 i) (hfix131_108 i) _)
      ⟨131, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 5 hp) Q2.T131_108_2 Q2.hfix131_108_2 Q2.hinj131_108_2
      Q2.hcardT131_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_108_2 i) (Q2.hfix131_108_2 i) _)
      colCert_131_108_5.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_108_10 (hp : 10 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp)) T131_108
      hfix131_108 hinj131_108 hcardT131_108
      (fun i => conj_mem_of_fixedPoints _ _ (T131_108 i) (hfix131_108 i) _)
      ⟨131, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 10 hp) Q2.T131_108_2 Q2.hfix131_108_2 Q2.hinj131_108_2
      Q2.hcardT131_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_108_2 i) (Q2.hfix131_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 10 (transLenTr ⟨108, by decide⟩ 10 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T131_108 = colFn colCertDiv_131_108_10.D1 (m := 5) from colCertDiv_131_108_10.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 10 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T131_108_2 = colFn colCertDiv_131_108_10.D2 (m := 5) from colCertDiv_131_108_10.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_108_10_match


theorem leaf_131_108_15 (hp : 15 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp)) T131_108
      hfix131_108 hinj131_108 hcardT131_108
      (fun i => conj_mem_of_fixedPoints _ _ (T131_108 i) (hfix131_108 i) _)
      ⟨131, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 15 hp) Q2.T131_108_2 Q2.hfix131_108_2 Q2.hinj131_108_2
      Q2.hcardT131_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_108_2 i) (Q2.hfix131_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 15 (transLenTr ⟨108, by decide⟩ 15 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T131_108 = colFn colCertDiv_131_108_15.D1 (m := 5) from colCertDiv_131_108_15.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 15 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T131_108_2 = colFn colCertDiv_131_108_15.D2 (m := 5) from colCertDiv_131_108_15.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_108_15_match


theorem leaf_131_108_20 (hp : 20 < (Q2.transData.getD 108 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨131, by decide⟩ : Fin 148) ⟨108, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp)) T131_108
      hfix131_108 hinj131_108 hcardT131_108
      (fun i => conj_mem_of_fixedPoints _ _ (T131_108 i) (hfix131_108 i) _)
      ⟨131, by decide⟩ ⟨108, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨108, by decide⟩ 20 hp) Q2.T131_108_2 Q2.hfix131_108_2 Q2.hinj131_108_2
      Q2.hcardT131_108_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_108_2 i) (Q2.hfix131_108_2 i) _)
      ?_).symm
  rw [show colData1 (⟨131, by decide⟩ : Fin 148)
        ((colE1 ⟨108, by decide⟩ 20 (transLenTr ⟨108, by decide⟩ 20 hp) : ↥(reps ⟨108, by decide⟩)) : Coordinate 1)
        T131_108 = colFn colCertDiv_131_108_20.D1 (m := 5) from colCertDiv_131_108_20.bind1,
    show colData2 (⟨131, by decide⟩ : Fin 148)
        ((colE2 ⟨108, by decide⟩ 20 hp : ↥(Q2.reps ⟨108, by decide⟩)) : Coordinate 2)
        Q2.T131_108_2 = colFn colCertDiv_131_108_20.D2 (m := 5) from colCertDiv_131_108_20.bind2]
  rw [alnId_131 j hj]
  exact fastcode_of_div ⟨131, by decide⟩ _ _ _
    ((alnId_131 j hj) ▸ Q2.listedAt (⟨131, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨131, by decide⟩ : Fin 148) hj hq).1) colCertDiv_131_108_20_match


theorem leaf_131_110_0 (hp : 0 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 0 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_1 (hp : 1 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 1 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_2 (hp : 2 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 2 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_3 (hp : 3 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 3 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_4 (hp : 4 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 4 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_5 (hp : 5 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 5 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_5.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_10 (hp : 10 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 10 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_10.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_15 (hp : 15 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 15 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_15.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_20 (hp : 20 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 20 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_20.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_25 (hp : 25 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 25 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 25 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_25.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_50 (hp : 50 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 50 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 50 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_50.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_75 (hp : 75 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 75 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 75 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_75.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_110_100 (hp : 100 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 100 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp)) T131_110
      hfix131_110 hinj131_110 hcardT131_110
      (fun i => conj_mem_of_fixedPoints _ _ (T131_110 i) (hfix131_110 i) _)
      ⟨131, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 100 hp) Q2.T131_110_2 Q2.hfix131_110_2 Q2.hinj131_110_2
      Q2.hcardT131_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_110_2 i) (Q2.hfix131_110_2 i) _)
      colCert_131_110_100.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_0 (hp : 0 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 0 (transLenTr ⟨131, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 0 (transLenTr ⟨131, by decide⟩ 0 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 0 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_1 (hp : 1 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 1 (transLenTr ⟨131, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 1 (transLenTr ⟨131, by decide⟩ 1 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 1 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_2 (hp : 2 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 2 (transLenTr ⟨131, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 2 (transLenTr ⟨131, by decide⟩ 2 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 2 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_3 (hp : 3 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 3 (transLenTr ⟨131, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 3 (transLenTr ⟨131, by decide⟩ 3 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 3 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_4 (hp : 4 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 4 (transLenTr ⟨131, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 4 (transLenTr ⟨131, by decide⟩ 4 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 4 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_5 (hp : 5 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 5 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 5 (transLenTr ⟨131, by decide⟩ 5 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 5 (transLenTr ⟨131, by decide⟩ 5 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 5 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_5.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_6 (hp : 6 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 6 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 6 (transLenTr ⟨131, by decide⟩ 6 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 6 (transLenTr ⟨131, by decide⟩ 6 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 6 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_6.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_7 (hp : 7 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 7 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 7 (transLenTr ⟨131, by decide⟩ 7 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 7 (transLenTr ⟨131, by decide⟩ 7 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 7 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_7.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_8 (hp : 8 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 8 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 8 (transLenTr ⟨131, by decide⟩ 8 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 8 (transLenTr ⟨131, by decide⟩ 8 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 8 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_8.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_9 (hp : 9 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 9 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 9 (transLenTr ⟨131, by decide⟩ 9 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 9 (transLenTr ⟨131, by decide⟩ 9 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 9 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_9.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_10 (hp : 10 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 10 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 10 (transLenTr ⟨131, by decide⟩ 10 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 10 (transLenTr ⟨131, by decide⟩ 10 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 10 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_10.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_11 (hp : 11 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 11 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 11 (transLenTr ⟨131, by decide⟩ 11 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 11 (transLenTr ⟨131, by decide⟩ 11 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 11 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_11.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_12 (hp : 12 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 12 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 12 (transLenTr ⟨131, by decide⟩ 12 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 12 (transLenTr ⟨131, by decide⟩ 12 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 12 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_12.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_13 (hp : 13 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 13 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 13 (transLenTr ⟨131, by decide⟩ 13 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 13 (transLenTr ⟨131, by decide⟩ 13 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 13 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_13.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_14 (hp : 14 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 14 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 14 (transLenTr ⟨131, by decide⟩ 14 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 14 (transLenTr ⟨131, by decide⟩ 14 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 14 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_14.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_15 (hp : 15 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 15 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 15 (transLenTr ⟨131, by decide⟩ 15 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 15 (transLenTr ⟨131, by decide⟩ 15 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 15 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_15.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_16 (hp : 16 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 16 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 16 (transLenTr ⟨131, by decide⟩ 16 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 16 (transLenTr ⟨131, by decide⟩ 16 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 16 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_16.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_17 (hp : 17 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 17 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 17 (transLenTr ⟨131, by decide⟩ 17 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 17 (transLenTr ⟨131, by decide⟩ 17 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 17 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_17.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_18 (hp : 18 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 18 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 18 (transLenTr ⟨131, by decide⟩ 18 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 18 (transLenTr ⟨131, by decide⟩ 18 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 18 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_18.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_19 (hp : 19 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 19 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 19 (transLenTr ⟨131, by decide⟩ 19 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 19 (transLenTr ⟨131, by decide⟩ 19 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 19 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_19.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_20 (hp : 20 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 20 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 20 (transLenTr ⟨131, by decide⟩ 20 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 20 (transLenTr ⟨131, by decide⟩ 20 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 20 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_20.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_21 (hp : 21 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 21 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 21 (transLenTr ⟨131, by decide⟩ 21 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 21 (transLenTr ⟨131, by decide⟩ 21 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 21 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_21.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_22 (hp : 22 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 22 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 22 (transLenTr ⟨131, by decide⟩ 22 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 22 (transLenTr ⟨131, by decide⟩ 22 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 22 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_22.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_23 (hp : 23 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 23 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 23 (transLenTr ⟨131, by decide⟩ 23 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 23 (transLenTr ⟨131, by decide⟩ 23 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 23 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_23.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_131_24 (hp : 24 < (Q2.transData.getD 131 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ 24 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ 24 (transLenTr ⟨131, by decide⟩ 24 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨131, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨131, by decide⟩ 24 (transLenTr ⟨131, by decide⟩ 24 hp)) T131_131
      hfix131_131 hinj131_131 hcardT131_131
      (fun i => conj_mem_of_fixedPoints _ _ (T131_131 i) (hfix131_131 i) _)
      ⟨131, by decide⟩ ⟨131, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨131, by decide⟩ 24 hp) Q2.T131_131_2 Q2.hfix131_131_2 Q2.hinj131_131_2
      Q2.hcardT131_131_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_131_2 i) (Q2.hfix131_131_2 i) _)
      colCert_131_131_24.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_132_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T132_4
      hfix132_4 hinj132_4 hcardT132_4
      (fun i => conj_mem_of_fixedPoints _ _ (T132_4 i) (hfix132_4 i) _)
      ⟨132, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T132_4_2 Q2.hfix132_4_2 Q2.hinj132_4_2
      Q2.hcardT132_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_4_2 i) (Q2.hfix132_4_2 i) _)
      colCert_132_4_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T132_4
      hfix132_4 hinj132_4 hcardT132_4
      (fun i => conj_mem_of_fixedPoints _ _ (T132_4 i) (hfix132_4 i) _)
      ⟨132, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T132_4_2 Q2.hfix132_4_2 Q2.hinj132_4_2
      Q2.hcardT132_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_4_2 i) (Q2.hfix132_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T132_4 = colFn colCertDiv_132_4_1.D1 (m := 5) from colCertDiv_132_4_1.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 1 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T132_4_2 = colFn colCertDiv_132_4_1.D2 (m := 5) from colCertDiv_132_4_1.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_4_1_match


theorem leaf_132_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T132_4
      hfix132_4 hinj132_4 hcardT132_4
      (fun i => conj_mem_of_fixedPoints _ _ (T132_4 i) (hfix132_4 i) _)
      ⟨132, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T132_4_2 Q2.hfix132_4_2 Q2.hinj132_4_2
      Q2.hcardT132_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_4_2 i) (Q2.hfix132_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T132_4 = colFn colCertDiv_132_4_2.D1 (m := 5) from colCertDiv_132_4_2.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 2 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T132_4_2 = colFn colCertDiv_132_4_2.D2 (m := 5) from colCertDiv_132_4_2.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_4_2_match


theorem leaf_132_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T132_4
      hfix132_4 hinj132_4 hcardT132_4
      (fun i => conj_mem_of_fixedPoints _ _ (T132_4 i) (hfix132_4 i) _)
      ⟨132, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T132_4_2 Q2.hfix132_4_2 Q2.hinj132_4_2
      Q2.hcardT132_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_4_2 i) (Q2.hfix132_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T132_4 = colFn colCertDiv_132_4_3.D1 (m := 5) from colCertDiv_132_4_3.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 3 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T132_4_2 = colFn colCertDiv_132_4_3.D2 (m := 5) from colCertDiv_132_4_3.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_4_3_match


theorem leaf_132_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T132_4
      hfix132_4 hinj132_4 hcardT132_4
      (fun i => conj_mem_of_fixedPoints _ _ (T132_4 i) (hfix132_4 i) _)
      ⟨132, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T132_4_2 Q2.hfix132_4_2 Q2.hinj132_4_2
      Q2.hcardT132_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_4_2 i) (Q2.hfix132_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T132_4 = colFn colCertDiv_132_4_4.D1 (m := 5) from colCertDiv_132_4_4.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 4 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T132_4_2 = colFn colCertDiv_132_4_4.D2 (m := 5) from colCertDiv_132_4_4.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_4_4_match


theorem leaf_132_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T132_10
      hfix132_10 hinj132_10 hcardT132_10
      (fun i => conj_mem_of_fixedPoints _ _ (T132_10 i) (hfix132_10 i) _)
      ⟨132, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T132_10_2 Q2.hfix132_10_2 Q2.hinj132_10_2
      Q2.hcardT132_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_10_2 i) (Q2.hfix132_10_2 i) _)
      colCert_132_10_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T132_10
      hfix132_10 hinj132_10 hcardT132_10
      (fun i => conj_mem_of_fixedPoints _ _ (T132_10 i) (hfix132_10 i) _)
      ⟨132, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T132_10_2 Q2.hfix132_10_2 Q2.hinj132_10_2
      Q2.hcardT132_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_10_2 i) (Q2.hfix132_10_2 i) _)
      colCert_132_10_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T132_10
      hfix132_10 hinj132_10 hcardT132_10
      (fun i => conj_mem_of_fixedPoints _ _ (T132_10 i) (hfix132_10 i) _)
      ⟨132, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T132_10_2 Q2.hfix132_10_2 Q2.hinj132_10_2
      Q2.hcardT132_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_10_2 i) (Q2.hfix132_10_2 i) _)
      colCert_132_10_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T132_10
      hfix132_10 hinj132_10 hcardT132_10
      (fun i => conj_mem_of_fixedPoints _ _ (T132_10 i) (hfix132_10 i) _)
      ⟨132, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T132_10_2 Q2.hfix132_10_2 Q2.hinj132_10_2
      Q2.hcardT132_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_10_2 i) (Q2.hfix132_10_2 i) _)
      colCert_132_10_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T132_10
      hfix132_10 hinj132_10 hcardT132_10
      (fun i => conj_mem_of_fixedPoints _ _ (T132_10 i) (hfix132_10 i) _)
      ⟨132, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T132_10_2 Q2.hfix132_10_2 Q2.hinj132_10_2
      Q2.hcardT132_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_10_2 i) (Q2.hfix132_10_2 i) _)
      colCert_132_10_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T132_12
      hfix132_12 hinj132_12 hcardT132_12
      (fun i => conj_mem_of_fixedPoints _ _ (T132_12 i) (hfix132_12 i) _)
      ⟨132, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T132_12_2 Q2.hfix132_12_2 Q2.hinj132_12_2
      Q2.hcardT132_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_12_2 i) (Q2.hfix132_12_2 i) _)
      colCert_132_12_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T132_12
      hfix132_12 hinj132_12 hcardT132_12
      (fun i => conj_mem_of_fixedPoints _ _ (T132_12 i) (hfix132_12 i) _)
      ⟨132, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T132_12_2 Q2.hfix132_12_2 Q2.hinj132_12_2
      Q2.hcardT132_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_12_2 i) (Q2.hfix132_12_2 i) _)
      colCert_132_12_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T132_12
      hfix132_12 hinj132_12 hcardT132_12
      (fun i => conj_mem_of_fixedPoints _ _ (T132_12 i) (hfix132_12 i) _)
      ⟨132, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T132_12_2 Q2.hfix132_12_2 Q2.hinj132_12_2
      Q2.hcardT132_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_12_2 i) (Q2.hfix132_12_2 i) _)
      colCert_132_12_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T132_12
      hfix132_12 hinj132_12 hcardT132_12
      (fun i => conj_mem_of_fixedPoints _ _ (T132_12 i) (hfix132_12 i) _)
      ⟨132, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T132_12_2 Q2.hfix132_12_2 Q2.hinj132_12_2
      Q2.hcardT132_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_12_2 i) (Q2.hfix132_12_2 i) _)
      colCert_132_12_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T132_12
      hfix132_12 hinj132_12 hcardT132_12
      (fun i => conj_mem_of_fixedPoints _ _ (T132_12 i) (hfix132_12 i) _)
      ⟨132, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T132_12_2 Q2.hfix132_12_2 Q2.hinj132_12_2
      Q2.hcardT132_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_12_2 i) (Q2.hfix132_12_2 i) _)
      colCert_132_12_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T132_22
      hfix132_22 hinj132_22 hcardT132_22
      (fun i => conj_mem_of_fixedPoints _ _ (T132_22 i) (hfix132_22 i) _)
      ⟨132, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T132_22_2 Q2.hfix132_22_2 Q2.hinj132_22_2
      Q2.hcardT132_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_22_2 i) (Q2.hfix132_22_2 i) _)
      colCert_132_22_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T132_22
      hfix132_22 hinj132_22 hcardT132_22
      (fun i => conj_mem_of_fixedPoints _ _ (T132_22 i) (hfix132_22 i) _)
      ⟨132, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T132_22_2 Q2.hfix132_22_2 Q2.hinj132_22_2
      Q2.hcardT132_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_22_2 i) (Q2.hfix132_22_2 i) _)
      colCert_132_22_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T132_22
      hfix132_22 hinj132_22 hcardT132_22
      (fun i => conj_mem_of_fixedPoints _ _ (T132_22 i) (hfix132_22 i) _)
      ⟨132, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T132_22_2 Q2.hfix132_22_2 Q2.hinj132_22_2
      Q2.hcardT132_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_22_2 i) (Q2.hfix132_22_2 i) _)
      colCert_132_22_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T132_22
      hfix132_22 hinj132_22 hcardT132_22
      (fun i => conj_mem_of_fixedPoints _ _ (T132_22 i) (hfix132_22 i) _)
      ⟨132, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T132_22_2 Q2.hfix132_22_2 Q2.hinj132_22_2
      Q2.hcardT132_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_22_2 i) (Q2.hfix132_22_2 i) _)
      colCert_132_22_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T132_22
      hfix132_22 hinj132_22 hcardT132_22
      (fun i => conj_mem_of_fixedPoints _ _ (T132_22 i) (hfix132_22 i) _)
      ⟨132, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T132_22_2 Q2.hfix132_22_2 Q2.hinj132_22_2
      Q2.hcardT132_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_22_2 i) (Q2.hfix132_22_2 i) _)
      colCert_132_22_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T132_22
      hfix132_22 hinj132_22 hcardT132_22
      (fun i => conj_mem_of_fixedPoints _ _ (T132_22 i) (hfix132_22 i) _)
      ⟨132, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T132_22_2 Q2.hfix132_22_2 Q2.hinj132_22_2
      Q2.hcardT132_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_22_2 i) (Q2.hfix132_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T132_22 = colFn colCertDiv_132_22_5.D1 (m := 5) from colCertDiv_132_22_5.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 5 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T132_22_2 = colFn colCertDiv_132_22_5.D2 (m := 5) from colCertDiv_132_22_5.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_22_5_match


theorem leaf_132_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T132_22
      hfix132_22 hinj132_22 hcardT132_22
      (fun i => conj_mem_of_fixedPoints _ _ (T132_22 i) (hfix132_22 i) _)
      ⟨132, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T132_22_2 Q2.hfix132_22_2 Q2.hinj132_22_2
      Q2.hcardT132_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_22_2 i) (Q2.hfix132_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T132_22 = colFn colCertDiv_132_22_10.D1 (m := 5) from colCertDiv_132_22_10.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 10 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T132_22_2 = colFn colCertDiv_132_22_10.D2 (m := 5) from colCertDiv_132_22_10.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_22_10_match


theorem leaf_132_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T132_22
      hfix132_22 hinj132_22 hcardT132_22
      (fun i => conj_mem_of_fixedPoints _ _ (T132_22 i) (hfix132_22 i) _)
      ⟨132, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T132_22_2 Q2.hfix132_22_2 Q2.hinj132_22_2
      Q2.hcardT132_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_22_2 i) (Q2.hfix132_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T132_22 = colFn colCertDiv_132_22_15.D1 (m := 5) from colCertDiv_132_22_15.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 15 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T132_22_2 = colFn colCertDiv_132_22_15.D2 (m := 5) from colCertDiv_132_22_15.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_22_15_match


theorem leaf_132_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T132_22
      hfix132_22 hinj132_22 hcardT132_22
      (fun i => conj_mem_of_fixedPoints _ _ (T132_22 i) (hfix132_22 i) _)
      ⟨132, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T132_22_2 Q2.hfix132_22_2 Q2.hinj132_22_2
      Q2.hcardT132_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_22_2 i) (Q2.hfix132_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T132_22 = colFn colCertDiv_132_22_20.D1 (m := 5) from colCertDiv_132_22_20.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 20 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T132_22_2 = colFn colCertDiv_132_22_20.D2 (m := 5) from colCertDiv_132_22_20.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_22_20_match


theorem leaf_132_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T132_31
      hfix132_31 hinj132_31 hcardT132_31
      (fun i => conj_mem_of_fixedPoints _ _ (T132_31 i) (hfix132_31 i) _)
      ⟨132, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T132_31_2 Q2.hfix132_31_2 Q2.hinj132_31_2
      Q2.hcardT132_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_31_2 i) (Q2.hfix132_31_2 i) _)
      colCert_132_31_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T132_31
      hfix132_31 hinj132_31 hcardT132_31
      (fun i => conj_mem_of_fixedPoints _ _ (T132_31 i) (hfix132_31 i) _)
      ⟨132, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T132_31_2 Q2.hfix132_31_2 Q2.hinj132_31_2
      Q2.hcardT132_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_31_2 i) (Q2.hfix132_31_2 i) _)
      colCert_132_31_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T132_31
      hfix132_31 hinj132_31 hcardT132_31
      (fun i => conj_mem_of_fixedPoints _ _ (T132_31 i) (hfix132_31 i) _)
      ⟨132, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T132_31_2 Q2.hfix132_31_2 Q2.hinj132_31_2
      Q2.hcardT132_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_31_2 i) (Q2.hfix132_31_2 i) _)
      colCert_132_31_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T132_31
      hfix132_31 hinj132_31 hcardT132_31
      (fun i => conj_mem_of_fixedPoints _ _ (T132_31 i) (hfix132_31 i) _)
      ⟨132, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T132_31_2 Q2.hfix132_31_2 Q2.hinj132_31_2
      Q2.hcardT132_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_31_2 i) (Q2.hfix132_31_2 i) _)
      colCert_132_31_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T132_31
      hfix132_31 hinj132_31 hcardT132_31
      (fun i => conj_mem_of_fixedPoints _ _ (T132_31 i) (hfix132_31 i) _)
      ⟨132, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T132_31_2 Q2.hfix132_31_2 Q2.hinj132_31_2
      Q2.hcardT132_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_31_2 i) (Q2.hfix132_31_2 i) _)
      colCert_132_31_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T132_31
      hfix132_31 hinj132_31 hcardT132_31
      (fun i => conj_mem_of_fixedPoints _ _ (T132_31 i) (hfix132_31 i) _)
      ⟨132, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T132_31_2 Q2.hfix132_31_2 Q2.hinj132_31_2
      Q2.hcardT132_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_31_2 i) (Q2.hfix132_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T132_31 = colFn colCertDiv_132_31_5.D1 (m := 5) from colCertDiv_132_31_5.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 5 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T132_31_2 = colFn colCertDiv_132_31_5.D2 (m := 5) from colCertDiv_132_31_5.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_31_5_match


theorem leaf_132_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T132_31
      hfix132_31 hinj132_31 hcardT132_31
      (fun i => conj_mem_of_fixedPoints _ _ (T132_31 i) (hfix132_31 i) _)
      ⟨132, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T132_31_2 Q2.hfix132_31_2 Q2.hinj132_31_2
      Q2.hcardT132_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_31_2 i) (Q2.hfix132_31_2 i) _)
      colCert_132_31_10.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T132_31
      hfix132_31 hinj132_31 hcardT132_31
      (fun i => conj_mem_of_fixedPoints _ _ (T132_31 i) (hfix132_31 i) _)
      ⟨132, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T132_31_2 Q2.hfix132_31_2 Q2.hinj132_31_2
      Q2.hcardT132_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_31_2 i) (Q2.hfix132_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T132_31 = colFn colCertDiv_132_31_15.D1 (m := 5) from colCertDiv_132_31_15.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 15 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T132_31_2 = colFn colCertDiv_132_31_15.D2 (m := 5) from colCertDiv_132_31_15.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_31_15_match


theorem leaf_132_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T132_31
      hfix132_31 hinj132_31 hcardT132_31
      (fun i => conj_mem_of_fixedPoints _ _ (T132_31 i) (hfix132_31 i) _)
      ⟨132, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T132_31_2 Q2.hfix132_31_2 Q2.hinj132_31_2
      Q2.hcardT132_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_31_2 i) (Q2.hfix132_31_2 i) _)
      colCert_132_31_20.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T132_35
      hfix132_35 hinj132_35 hcardT132_35
      (fun i => conj_mem_of_fixedPoints _ _ (T132_35 i) (hfix132_35 i) _)
      ⟨132, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T132_35_2 Q2.hfix132_35_2 Q2.hinj132_35_2
      Q2.hcardT132_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_35_2 i) (Q2.hfix132_35_2 i) _)
      colCert_132_35_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T132_35
      hfix132_35 hinj132_35 hcardT132_35
      (fun i => conj_mem_of_fixedPoints _ _ (T132_35 i) (hfix132_35 i) _)
      ⟨132, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T132_35_2 Q2.hfix132_35_2 Q2.hinj132_35_2
      Q2.hcardT132_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_35_2 i) (Q2.hfix132_35_2 i) _)
      colCert_132_35_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T132_35
      hfix132_35 hinj132_35 hcardT132_35
      (fun i => conj_mem_of_fixedPoints _ _ (T132_35 i) (hfix132_35 i) _)
      ⟨132, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T132_35_2 Q2.hfix132_35_2 Q2.hinj132_35_2
      Q2.hcardT132_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_35_2 i) (Q2.hfix132_35_2 i) _)
      colCert_132_35_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T132_35
      hfix132_35 hinj132_35 hcardT132_35
      (fun i => conj_mem_of_fixedPoints _ _ (T132_35 i) (hfix132_35 i) _)
      ⟨132, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T132_35_2 Q2.hfix132_35_2 Q2.hinj132_35_2
      Q2.hcardT132_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_35_2 i) (Q2.hfix132_35_2 i) _)
      colCert_132_35_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T132_35
      hfix132_35 hinj132_35 hcardT132_35
      (fun i => conj_mem_of_fixedPoints _ _ (T132_35 i) (hfix132_35 i) _)
      ⟨132, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T132_35_2 Q2.hfix132_35_2 Q2.hinj132_35_2
      Q2.hcardT132_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_35_2 i) (Q2.hfix132_35_2 i) _)
      colCert_132_35_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T132_35
      hfix132_35 hinj132_35 hcardT132_35
      (fun i => conj_mem_of_fixedPoints _ _ (T132_35 i) (hfix132_35 i) _)
      ⟨132, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T132_35_2 Q2.hfix132_35_2 Q2.hinj132_35_2
      Q2.hcardT132_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_35_2 i) (Q2.hfix132_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T132_35 = colFn colCertDiv_132_35_5.D1 (m := 5) from colCertDiv_132_35_5.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 5 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T132_35_2 = colFn colCertDiv_132_35_5.D2 (m := 5) from colCertDiv_132_35_5.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_35_5_match


theorem leaf_132_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T132_35
      hfix132_35 hinj132_35 hcardT132_35
      (fun i => conj_mem_of_fixedPoints _ _ (T132_35 i) (hfix132_35 i) _)
      ⟨132, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T132_35_2 Q2.hfix132_35_2 Q2.hinj132_35_2
      Q2.hcardT132_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_35_2 i) (Q2.hfix132_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T132_35 = colFn colCertDiv_132_35_10.D1 (m := 5) from colCertDiv_132_35_10.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 10 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T132_35_2 = colFn colCertDiv_132_35_10.D2 (m := 5) from colCertDiv_132_35_10.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_35_10_match


theorem leaf_132_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T132_35
      hfix132_35 hinj132_35 hcardT132_35
      (fun i => conj_mem_of_fixedPoints _ _ (T132_35 i) (hfix132_35 i) _)
      ⟨132, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T132_35_2 Q2.hfix132_35_2 Q2.hinj132_35_2
      Q2.hcardT132_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_35_2 i) (Q2.hfix132_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T132_35 = colFn colCertDiv_132_35_15.D1 (m := 5) from colCertDiv_132_35_15.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 15 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T132_35_2 = colFn colCertDiv_132_35_15.D2 (m := 5) from colCertDiv_132_35_15.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_35_15_match


theorem leaf_132_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T132_35
      hfix132_35 hinj132_35 hcardT132_35
      (fun i => conj_mem_of_fixedPoints _ _ (T132_35 i) (hfix132_35 i) _)
      ⟨132, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T132_35_2 Q2.hfix132_35_2 Q2.hinj132_35_2
      Q2.hcardT132_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_35_2 i) (Q2.hfix132_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T132_35 = colFn colCertDiv_132_35_20.D1 (m := 5) from colCertDiv_132_35_20.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 20 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T132_35_2 = colFn colCertDiv_132_35_20.D2 (m := 5) from colCertDiv_132_35_20.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_35_20_match


theorem leaf_132_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T132_38
      hfix132_38 hinj132_38 hcardT132_38
      (fun i => conj_mem_of_fixedPoints _ _ (T132_38 i) (hfix132_38 i) _)
      ⟨132, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T132_38_2 Q2.hfix132_38_2 Q2.hinj132_38_2
      Q2.hcardT132_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_38_2 i) (Q2.hfix132_38_2 i) _)
      colCert_132_38_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T132_38
      hfix132_38 hinj132_38 hcardT132_38
      (fun i => conj_mem_of_fixedPoints _ _ (T132_38 i) (hfix132_38 i) _)
      ⟨132, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T132_38_2 Q2.hfix132_38_2 Q2.hinj132_38_2
      Q2.hcardT132_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_38_2 i) (Q2.hfix132_38_2 i) _)
      colCert_132_38_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T132_38
      hfix132_38 hinj132_38 hcardT132_38
      (fun i => conj_mem_of_fixedPoints _ _ (T132_38 i) (hfix132_38 i) _)
      ⟨132, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T132_38_2 Q2.hfix132_38_2 Q2.hinj132_38_2
      Q2.hcardT132_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_38_2 i) (Q2.hfix132_38_2 i) _)
      colCert_132_38_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T132_38
      hfix132_38 hinj132_38 hcardT132_38
      (fun i => conj_mem_of_fixedPoints _ _ (T132_38 i) (hfix132_38 i) _)
      ⟨132, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T132_38_2 Q2.hfix132_38_2 Q2.hinj132_38_2
      Q2.hcardT132_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_38_2 i) (Q2.hfix132_38_2 i) _)
      colCert_132_38_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T132_38
      hfix132_38 hinj132_38 hcardT132_38
      (fun i => conj_mem_of_fixedPoints _ _ (T132_38 i) (hfix132_38 i) _)
      ⟨132, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T132_38_2 Q2.hfix132_38_2 Q2.hinj132_38_2
      Q2.hcardT132_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_38_2 i) (Q2.hfix132_38_2 i) _)
      colCert_132_38_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T132_38
      hfix132_38 hinj132_38 hcardT132_38
      (fun i => conj_mem_of_fixedPoints _ _ (T132_38 i) (hfix132_38 i) _)
      ⟨132, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T132_38_2 Q2.hfix132_38_2 Q2.hinj132_38_2
      Q2.hcardT132_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_38_2 i) (Q2.hfix132_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T132_38 = colFn colCertDiv_132_38_5.D1 (m := 5) from colCertDiv_132_38_5.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T132_38_2 = colFn colCertDiv_132_38_5.D2 (m := 5) from colCertDiv_132_38_5.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_38_5_match


theorem leaf_132_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T132_38
      hfix132_38 hinj132_38 hcardT132_38
      (fun i => conj_mem_of_fixedPoints _ _ (T132_38 i) (hfix132_38 i) _)
      ⟨132, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T132_38_2 Q2.hfix132_38_2 Q2.hinj132_38_2
      Q2.hcardT132_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_38_2 i) (Q2.hfix132_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T132_38 = colFn colCertDiv_132_38_10.D1 (m := 5) from colCertDiv_132_38_10.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T132_38_2 = colFn colCertDiv_132_38_10.D2 (m := 5) from colCertDiv_132_38_10.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_38_10_match


theorem leaf_132_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T132_38
      hfix132_38 hinj132_38 hcardT132_38
      (fun i => conj_mem_of_fixedPoints _ _ (T132_38 i) (hfix132_38 i) _)
      ⟨132, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T132_38_2 Q2.hfix132_38_2 Q2.hinj132_38_2
      Q2.hcardT132_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_38_2 i) (Q2.hfix132_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T132_38 = colFn colCertDiv_132_38_15.D1 (m := 5) from colCertDiv_132_38_15.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T132_38_2 = colFn colCertDiv_132_38_15.D2 (m := 5) from colCertDiv_132_38_15.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_38_15_match


theorem leaf_132_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T132_38
      hfix132_38 hinj132_38 hcardT132_38
      (fun i => conj_mem_of_fixedPoints _ _ (T132_38 i) (hfix132_38 i) _)
      ⟨132, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T132_38_2 Q2.hfix132_38_2 Q2.hinj132_38_2
      Q2.hcardT132_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_38_2 i) (Q2.hfix132_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T132_38 = colFn colCertDiv_132_38_20.D1 (m := 5) from colCertDiv_132_38_20.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T132_38_2 = colFn colCertDiv_132_38_20.D2 (m := 5) from colCertDiv_132_38_20.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_38_20_match


theorem leaf_132_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T132_47
      hfix132_47 hinj132_47 hcardT132_47
      (fun i => conj_mem_of_fixedPoints _ _ (T132_47 i) (hfix132_47 i) _)
      ⟨132, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T132_47_2 Q2.hfix132_47_2 Q2.hinj132_47_2
      Q2.hcardT132_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_47_2 i) (Q2.hfix132_47_2 i) _)
      colCert_132_47_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T132_47
      hfix132_47 hinj132_47 hcardT132_47
      (fun i => conj_mem_of_fixedPoints _ _ (T132_47 i) (hfix132_47 i) _)
      ⟨132, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T132_47_2 Q2.hfix132_47_2 Q2.hinj132_47_2
      Q2.hcardT132_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_47_2 i) (Q2.hfix132_47_2 i) _)
      colCert_132_47_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T132_47
      hfix132_47 hinj132_47 hcardT132_47
      (fun i => conj_mem_of_fixedPoints _ _ (T132_47 i) (hfix132_47 i) _)
      ⟨132, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T132_47_2 Q2.hfix132_47_2 Q2.hinj132_47_2
      Q2.hcardT132_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_47_2 i) (Q2.hfix132_47_2 i) _)
      colCert_132_47_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T132_47
      hfix132_47 hinj132_47 hcardT132_47
      (fun i => conj_mem_of_fixedPoints _ _ (T132_47 i) (hfix132_47 i) _)
      ⟨132, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T132_47_2 Q2.hfix132_47_2 Q2.hinj132_47_2
      Q2.hcardT132_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_47_2 i) (Q2.hfix132_47_2 i) _)
      colCert_132_47_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T132_47
      hfix132_47 hinj132_47 hcardT132_47
      (fun i => conj_mem_of_fixedPoints _ _ (T132_47 i) (hfix132_47 i) _)
      ⟨132, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T132_47_2 Q2.hfix132_47_2 Q2.hinj132_47_2
      Q2.hcardT132_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_47_2 i) (Q2.hfix132_47_2 i) _)
      colCert_132_47_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T132_47
      hfix132_47 hinj132_47 hcardT132_47
      (fun i => conj_mem_of_fixedPoints _ _ (T132_47 i) (hfix132_47 i) _)
      ⟨132, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T132_47_2 Q2.hfix132_47_2 Q2.hinj132_47_2
      Q2.hcardT132_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_47_2 i) (Q2.hfix132_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T132_47 = colFn colCertDiv_132_47_5.D1 (m := 5) from colCertDiv_132_47_5.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T132_47_2 = colFn colCertDiv_132_47_5.D2 (m := 5) from colCertDiv_132_47_5.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_47_5_match


theorem leaf_132_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T132_47
      hfix132_47 hinj132_47 hcardT132_47
      (fun i => conj_mem_of_fixedPoints _ _ (T132_47 i) (hfix132_47 i) _)
      ⟨132, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T132_47_2 Q2.hfix132_47_2 Q2.hinj132_47_2
      Q2.hcardT132_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_47_2 i) (Q2.hfix132_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T132_47 = colFn colCertDiv_132_47_10.D1 (m := 5) from colCertDiv_132_47_10.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T132_47_2 = colFn colCertDiv_132_47_10.D2 (m := 5) from colCertDiv_132_47_10.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_47_10_match


theorem leaf_132_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T132_47
      hfix132_47 hinj132_47 hcardT132_47
      (fun i => conj_mem_of_fixedPoints _ _ (T132_47 i) (hfix132_47 i) _)
      ⟨132, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T132_47_2 Q2.hfix132_47_2 Q2.hinj132_47_2
      Q2.hcardT132_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_47_2 i) (Q2.hfix132_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T132_47 = colFn colCertDiv_132_47_15.D1 (m := 5) from colCertDiv_132_47_15.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T132_47_2 = colFn colCertDiv_132_47_15.D2 (m := 5) from colCertDiv_132_47_15.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_47_15_match


theorem leaf_132_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T132_47
      hfix132_47 hinj132_47 hcardT132_47
      (fun i => conj_mem_of_fixedPoints _ _ (T132_47 i) (hfix132_47 i) _)
      ⟨132, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T132_47_2 Q2.hfix132_47_2 Q2.hinj132_47_2
      Q2.hcardT132_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_47_2 i) (Q2.hfix132_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T132_47 = colFn colCertDiv_132_47_20.D1 (m := 5) from colCertDiv_132_47_20.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T132_47_2 = colFn colCertDiv_132_47_20.D2 (m := 5) from colCertDiv_132_47_20.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_47_20_match


theorem leaf_132_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T132_49
      hfix132_49 hinj132_49 hcardT132_49
      (fun i => conj_mem_of_fixedPoints _ _ (T132_49 i) (hfix132_49 i) _)
      ⟨132, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T132_49_2 Q2.hfix132_49_2 Q2.hinj132_49_2
      Q2.hcardT132_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_49_2 i) (Q2.hfix132_49_2 i) _)
      colCert_132_49_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T132_49
      hfix132_49 hinj132_49 hcardT132_49
      (fun i => conj_mem_of_fixedPoints _ _ (T132_49 i) (hfix132_49 i) _)
      ⟨132, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T132_49_2 Q2.hfix132_49_2 Q2.hinj132_49_2
      Q2.hcardT132_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_49_2 i) (Q2.hfix132_49_2 i) _)
      colCert_132_49_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T132_49
      hfix132_49 hinj132_49 hcardT132_49
      (fun i => conj_mem_of_fixedPoints _ _ (T132_49 i) (hfix132_49 i) _)
      ⟨132, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T132_49_2 Q2.hfix132_49_2 Q2.hinj132_49_2
      Q2.hcardT132_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_49_2 i) (Q2.hfix132_49_2 i) _)
      colCert_132_49_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T132_49
      hfix132_49 hinj132_49 hcardT132_49
      (fun i => conj_mem_of_fixedPoints _ _ (T132_49 i) (hfix132_49 i) _)
      ⟨132, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T132_49_2 Q2.hfix132_49_2 Q2.hinj132_49_2
      Q2.hcardT132_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_49_2 i) (Q2.hfix132_49_2 i) _)
      colCert_132_49_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T132_49
      hfix132_49 hinj132_49 hcardT132_49
      (fun i => conj_mem_of_fixedPoints _ _ (T132_49 i) (hfix132_49 i) _)
      ⟨132, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T132_49_2 Q2.hfix132_49_2 Q2.hinj132_49_2
      Q2.hcardT132_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_49_2 i) (Q2.hfix132_49_2 i) _)
      colCert_132_49_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T132_49
      hfix132_49 hinj132_49 hcardT132_49
      (fun i => conj_mem_of_fixedPoints _ _ (T132_49 i) (hfix132_49 i) _)
      ⟨132, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T132_49_2 Q2.hfix132_49_2 Q2.hinj132_49_2
      Q2.hcardT132_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_49_2 i) (Q2.hfix132_49_2 i) _)
      colCert_132_49_5.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T132_49
      hfix132_49 hinj132_49 hcardT132_49
      (fun i => conj_mem_of_fixedPoints _ _ (T132_49 i) (hfix132_49 i) _)
      ⟨132, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T132_49_2 Q2.hfix132_49_2 Q2.hinj132_49_2
      Q2.hcardT132_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_49_2 i) (Q2.hfix132_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T132_49 = colFn colCertDiv_132_49_10.D1 (m := 5) from colCertDiv_132_49_10.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 10 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T132_49_2 = colFn colCertDiv_132_49_10.D2 (m := 5) from colCertDiv_132_49_10.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_49_10_match


theorem leaf_132_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T132_49
      hfix132_49 hinj132_49 hcardT132_49
      (fun i => conj_mem_of_fixedPoints _ _ (T132_49 i) (hfix132_49 i) _)
      ⟨132, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T132_49_2 Q2.hfix132_49_2 Q2.hinj132_49_2
      Q2.hcardT132_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_49_2 i) (Q2.hfix132_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T132_49 = colFn colCertDiv_132_49_15.D1 (m := 5) from colCertDiv_132_49_15.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 15 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T132_49_2 = colFn colCertDiv_132_49_15.D2 (m := 5) from colCertDiv_132_49_15.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_49_15_match


theorem leaf_132_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T132_49
      hfix132_49 hinj132_49 hcardT132_49
      (fun i => conj_mem_of_fixedPoints _ _ (T132_49 i) (hfix132_49 i) _)
      ⟨132, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T132_49_2 Q2.hfix132_49_2 Q2.hinj132_49_2
      Q2.hcardT132_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_49_2 i) (Q2.hfix132_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T132_49 = colFn colCertDiv_132_49_20.D1 (m := 5) from colCertDiv_132_49_20.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 20 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T132_49_2 = colFn colCertDiv_132_49_20.D2 (m := 5) from colCertDiv_132_49_20.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_49_20_match


theorem leaf_132_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T132_53
      hfix132_53 hinj132_53 hcardT132_53
      (fun i => conj_mem_of_fixedPoints _ _ (T132_53 i) (hfix132_53 i) _)
      ⟨132, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T132_53_2 Q2.hfix132_53_2 Q2.hinj132_53_2
      Q2.hcardT132_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_53_2 i) (Q2.hfix132_53_2 i) _)
      colCert_132_53_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T132_53
      hfix132_53 hinj132_53 hcardT132_53
      (fun i => conj_mem_of_fixedPoints _ _ (T132_53 i) (hfix132_53 i) _)
      ⟨132, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T132_53_2 Q2.hfix132_53_2 Q2.hinj132_53_2
      Q2.hcardT132_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_53_2 i) (Q2.hfix132_53_2 i) _)
      colCert_132_53_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T132_53
      hfix132_53 hinj132_53 hcardT132_53
      (fun i => conj_mem_of_fixedPoints _ _ (T132_53 i) (hfix132_53 i) _)
      ⟨132, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T132_53_2 Q2.hfix132_53_2 Q2.hinj132_53_2
      Q2.hcardT132_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_53_2 i) (Q2.hfix132_53_2 i) _)
      colCert_132_53_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T132_53
      hfix132_53 hinj132_53 hcardT132_53
      (fun i => conj_mem_of_fixedPoints _ _ (T132_53 i) (hfix132_53 i) _)
      ⟨132, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T132_53_2 Q2.hfix132_53_2 Q2.hinj132_53_2
      Q2.hcardT132_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_53_2 i) (Q2.hfix132_53_2 i) _)
      colCert_132_53_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T132_53
      hfix132_53 hinj132_53 hcardT132_53
      (fun i => conj_mem_of_fixedPoints _ _ (T132_53 i) (hfix132_53 i) _)
      ⟨132, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T132_53_2 Q2.hfix132_53_2 Q2.hinj132_53_2
      Q2.hcardT132_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_53_2 i) (Q2.hfix132_53_2 i) _)
      colCert_132_53_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T132_53
      hfix132_53 hinj132_53 hcardT132_53
      (fun i => conj_mem_of_fixedPoints _ _ (T132_53 i) (hfix132_53 i) _)
      ⟨132, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T132_53_2 Q2.hfix132_53_2 Q2.hinj132_53_2
      Q2.hcardT132_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_53_2 i) (Q2.hfix132_53_2 i) _)
      colCert_132_53_5.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T132_53
      hfix132_53 hinj132_53 hcardT132_53
      (fun i => conj_mem_of_fixedPoints _ _ (T132_53 i) (hfix132_53 i) _)
      ⟨132, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T132_53_2 Q2.hfix132_53_2 Q2.hinj132_53_2
      Q2.hcardT132_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_53_2 i) (Q2.hfix132_53_2 i) _)
      colCert_132_53_10.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T132_53
      hfix132_53 hinj132_53 hcardT132_53
      (fun i => conj_mem_of_fixedPoints _ _ (T132_53 i) (hfix132_53 i) _)
      ⟨132, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T132_53_2 Q2.hfix132_53_2 Q2.hinj132_53_2
      Q2.hcardT132_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_53_2 i) (Q2.hfix132_53_2 i) _)
      colCert_132_53_15.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T132_53
      hfix132_53 hinj132_53 hcardT132_53
      (fun i => conj_mem_of_fixedPoints _ _ (T132_53 i) (hfix132_53 i) _)
      ⟨132, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T132_53_2 Q2.hfix132_53_2 Q2.hinj132_53_2
      Q2.hcardT132_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_53_2 i) (Q2.hfix132_53_2 i) _)
      colCert_132_53_20.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_83_0 (hp : 0 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp)) T132_83
      hfix132_83 hinj132_83 hcardT132_83
      (fun i => conj_mem_of_fixedPoints _ _ (T132_83 i) (hfix132_83 i) _)
      ⟨132, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 0 hp) Q2.T132_83_2 Q2.hfix132_83_2 Q2.hinj132_83_2
      Q2.hcardT132_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_83_2 i) (Q2.hfix132_83_2 i) _)
      colCert_132_83_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_83_1 (hp : 1 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp)) T132_83
      hfix132_83 hinj132_83 hcardT132_83
      (fun i => conj_mem_of_fixedPoints _ _ (T132_83 i) (hfix132_83 i) _)
      ⟨132, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 1 hp) Q2.T132_83_2 Q2.hfix132_83_2 Q2.hinj132_83_2
      Q2.hcardT132_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_83_2 i) (Q2.hfix132_83_2 i) _)
      colCert_132_83_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_83_2 (hp : 2 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp)) T132_83
      hfix132_83 hinj132_83 hcardT132_83
      (fun i => conj_mem_of_fixedPoints _ _ (T132_83 i) (hfix132_83 i) _)
      ⟨132, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 2 hp) Q2.T132_83_2 Q2.hfix132_83_2 Q2.hinj132_83_2
      Q2.hcardT132_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_83_2 i) (Q2.hfix132_83_2 i) _)
      colCert_132_83_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_83_3 (hp : 3 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp)) T132_83
      hfix132_83 hinj132_83 hcardT132_83
      (fun i => conj_mem_of_fixedPoints _ _ (T132_83 i) (hfix132_83 i) _)
      ⟨132, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 3 hp) Q2.T132_83_2 Q2.hfix132_83_2 Q2.hinj132_83_2
      Q2.hcardT132_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_83_2 i) (Q2.hfix132_83_2 i) _)
      colCert_132_83_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_83_4 (hp : 4 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp)) T132_83
      hfix132_83 hinj132_83 hcardT132_83
      (fun i => conj_mem_of_fixedPoints _ _ (T132_83 i) (hfix132_83 i) _)
      ⟨132, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 4 hp) Q2.T132_83_2 Q2.hfix132_83_2 Q2.hinj132_83_2
      Q2.hcardT132_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_83_2 i) (Q2.hfix132_83_2 i) _)
      colCert_132_83_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_83_5 (hp : 5 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp)) T132_83
      hfix132_83 hinj132_83 hcardT132_83
      (fun i => conj_mem_of_fixedPoints _ _ (T132_83 i) (hfix132_83 i) _)
      ⟨132, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 5 hp) Q2.T132_83_2 Q2.hfix132_83_2 Q2.hinj132_83_2
      Q2.hcardT132_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_83_2 i) (Q2.hfix132_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T132_83 = colFn colCertDiv_132_83_5.D1 (m := 5) from colCertDiv_132_83_5.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 5 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T132_83_2 = colFn colCertDiv_132_83_5.D2 (m := 5) from colCertDiv_132_83_5.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_83_5_match


theorem leaf_132_83_10 (hp : 10 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp)) T132_83
      hfix132_83 hinj132_83 hcardT132_83
      (fun i => conj_mem_of_fixedPoints _ _ (T132_83 i) (hfix132_83 i) _)
      ⟨132, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 10 hp) Q2.T132_83_2 Q2.hfix132_83_2 Q2.hinj132_83_2
      Q2.hcardT132_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_83_2 i) (Q2.hfix132_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T132_83 = colFn colCertDiv_132_83_10.D1 (m := 5) from colCertDiv_132_83_10.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 10 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T132_83_2 = colFn colCertDiv_132_83_10.D2 (m := 5) from colCertDiv_132_83_10.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_83_10_match


theorem leaf_132_83_15 (hp : 15 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp)) T132_83
      hfix132_83 hinj132_83 hcardT132_83
      (fun i => conj_mem_of_fixedPoints _ _ (T132_83 i) (hfix132_83 i) _)
      ⟨132, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 15 hp) Q2.T132_83_2 Q2.hfix132_83_2 Q2.hinj132_83_2
      Q2.hcardT132_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_83_2 i) (Q2.hfix132_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T132_83 = colFn colCertDiv_132_83_15.D1 (m := 5) from colCertDiv_132_83_15.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 15 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T132_83_2 = colFn colCertDiv_132_83_15.D2 (m := 5) from colCertDiv_132_83_15.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_83_15_match


theorem leaf_132_83_20 (hp : 20 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp)) T132_83
      hfix132_83 hinj132_83 hcardT132_83
      (fun i => conj_mem_of_fixedPoints _ _ (T132_83 i) (hfix132_83 i) _)
      ⟨132, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 20 hp) Q2.T132_83_2 Q2.hfix132_83_2 Q2.hinj132_83_2
      Q2.hcardT132_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_83_2 i) (Q2.hfix132_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T132_83 = colFn colCertDiv_132_83_20.D1 (m := 5) from colCertDiv_132_83_20.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 20 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T132_83_2 = colFn colCertDiv_132_83_20.D2 (m := 5) from colCertDiv_132_83_20.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_83_20_match


theorem leaf_132_93_0 (hp : 0 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp)) T132_93
      hfix132_93 hinj132_93 hcardT132_93
      (fun i => conj_mem_of_fixedPoints _ _ (T132_93 i) (hfix132_93 i) _)
      ⟨132, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 0 hp) Q2.T132_93_2 Q2.hfix132_93_2 Q2.hinj132_93_2
      Q2.hcardT132_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_93_2 i) (Q2.hfix132_93_2 i) _)
      colCert_132_93_0.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_93_1 (hp : 1 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 1 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp)) T132_93
      hfix132_93 hinj132_93 hcardT132_93
      (fun i => conj_mem_of_fixedPoints _ _ (T132_93 i) (hfix132_93 i) _)
      ⟨132, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 1 hp) Q2.T132_93_2 Q2.hfix132_93_2 Q2.hinj132_93_2
      Q2.hcardT132_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_93_2 i) (Q2.hfix132_93_2 i) _)
      colCert_132_93_1.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_93_2 (hp : 2 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 2 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp)) T132_93
      hfix132_93 hinj132_93 hcardT132_93
      (fun i => conj_mem_of_fixedPoints _ _ (T132_93 i) (hfix132_93 i) _)
      ⟨132, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 2 hp) Q2.T132_93_2 Q2.hfix132_93_2 Q2.hinj132_93_2
      Q2.hcardT132_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_93_2 i) (Q2.hfix132_93_2 i) _)
      colCert_132_93_2.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_93_3 (hp : 3 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 3 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp)) T132_93
      hfix132_93 hinj132_93 hcardT132_93
      (fun i => conj_mem_of_fixedPoints _ _ (T132_93 i) (hfix132_93 i) _)
      ⟨132, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 3 hp) Q2.T132_93_2 Q2.hfix132_93_2 Q2.hinj132_93_2
      Q2.hcardT132_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_93_2 i) (Q2.hfix132_93_2 i) _)
      colCert_132_93_3.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_93_4 (hp : 4 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 4 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp)) T132_93
      hfix132_93 hinj132_93 hcardT132_93
      (fun i => conj_mem_of_fixedPoints _ _ (T132_93 i) (hfix132_93 i) _)
      ⟨132, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 4 hp) Q2.T132_93_2 Q2.hfix132_93_2 Q2.hinj132_93_2
      Q2.hcardT132_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_93_2 i) (Q2.hfix132_93_2 i) _)
      colCert_132_93_4.hD ?_).symm
  rw [alnId_132 j hj]


theorem leaf_132_93_5 (hp : 5 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 5 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp)) T132_93
      hfix132_93 hinj132_93 hcardT132_93
      (fun i => conj_mem_of_fixedPoints _ _ (T132_93 i) (hfix132_93 i) _)
      ⟨132, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 5 hp) Q2.T132_93_2 Q2.hfix132_93_2 Q2.hinj132_93_2
      Q2.hcardT132_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_93_2 i) (Q2.hfix132_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T132_93 = colFn colCertDiv_132_93_5.D1 (m := 5) from colCertDiv_132_93_5.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 5 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T132_93_2 = colFn colCertDiv_132_93_5.D2 (m := 5) from colCertDiv_132_93_5.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_93_5_match


theorem leaf_132_93_10 (hp : 10 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 10 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp)) T132_93
      hfix132_93 hinj132_93 hcardT132_93
      (fun i => conj_mem_of_fixedPoints _ _ (T132_93 i) (hfix132_93 i) _)
      ⟨132, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 10 hp) Q2.T132_93_2 Q2.hfix132_93_2 Q2.hinj132_93_2
      Q2.hcardT132_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_93_2 i) (Q2.hfix132_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T132_93 = colFn colCertDiv_132_93_10.D1 (m := 5) from colCertDiv_132_93_10.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 10 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T132_93_2 = colFn colCertDiv_132_93_10.D2 (m := 5) from colCertDiv_132_93_10.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_93_10_match


theorem leaf_132_93_15 (hp : 15 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 15 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp)) T132_93
      hfix132_93 hinj132_93 hcardT132_93
      (fun i => conj_mem_of_fixedPoints _ _ (T132_93 i) (hfix132_93 i) _)
      ⟨132, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 15 hp) Q2.T132_93_2 Q2.hfix132_93_2 Q2.hinj132_93_2
      Q2.hcardT132_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_93_2 i) (Q2.hfix132_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T132_93 = colFn colCertDiv_132_93_15.D1 (m := 5) from colCertDiv_132_93_15.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 15 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T132_93_2 = colFn colCertDiv_132_93_15.D2 (m := 5) from colCertDiv_132_93_15.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_93_15_match


theorem leaf_132_93_20 (hp : 20 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 20 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨132, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp)) T132_93
      hfix132_93 hinj132_93 hcardT132_93
      (fun i => conj_mem_of_fixedPoints _ _ (T132_93 i) (hfix132_93 i) _)
      ⟨132, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 20 hp) Q2.T132_93_2 Q2.hfix132_93_2 Q2.hinj132_93_2
      Q2.hcardT132_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_93_2 i) (Q2.hfix132_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨132, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T132_93 = colFn colCertDiv_132_93_20.D1 (m := 5) from colCertDiv_132_93_20.bind1,
    show colData2 (⟨132, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 20 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T132_93_2 = colFn colCertDiv_132_93_20.D2 (m := 5) from colCertDiv_132_93_20.bind2]
  rw [alnId_132 j hj]
  exact fastcode_of_div ⟨132, by decide⟩ _ _ _
    ((alnId_132 j hj) ▸ Q2.listedAt (⟨132, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨132, by decide⟩ : Fin 148) hj hq).1) colCertDiv_132_93_20_match


theorem leaf_132_97_0 (hp : 0 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 132 []).length)
    (hq : (normIsRep.getD 132 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 0 hp)
        (rowE2 (⟨132, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp))
        (rowE1 (⟨132, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨132, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨132, by decide⟩ (listedAt ⟨132, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp)) T132_97
      hfix132_97 hinj132_97 hcardT132_97
      (fun i => conj_mem_of_fixedPoints _ _ (T132_97 i) (hfix132_97 i) _)
      ⟨132, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨132, by decide⟩ (Q2.listedAt ⟨132, by decide⟩
        (alnCheck_rep ⟨132, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 0 hp) Q2.T132_97_2 Q2.hfix132_97_2 Q2.hinj132_97_2
      Q2.hcardT132_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T132_97_2 i) (Q2.hfix132_97_2 i) _)
      colCert_132_97_0.hD ?_).symm
  rw [alnId_132 j hj]


end LeanDring.P5Presentation
