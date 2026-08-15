/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C001
import LeanDring.P5.Data.ColRestCheap.C013
import LeanDring.P5.Data.ColRestCheap.C014
import LeanDring.P5.Data.ColRestCheap.C015
import LeanDring.P5.Data.ColRestCheap.C016
import LeanDring.P5.Data.ColRestCheap.C017
import LeanDring.P5.Data.EntryK.C024
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesAlign.C025
import LeanDring.P5.Data.SpeciesAlign.C026
import LeanDring.P5.Data.SpeciesDiv.C004
import LeanDring.P5.Data.SpeciesDiv.C005
import LeanDring.P5.Data.SpeciesDiv.C006
import LeanDring.P5.Data.SpeciesDiv.C007

/-! # Stage-5 leaves, chunk 20 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_109_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T109_10
      hfix109_10 hinj109_10 hcardT109_10
      (fun i => conj_mem_of_fixedPoints _ _ (T109_10 i) (hfix109_10 i) _)
      ⟨109, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T109_10_2 Q2.hfix109_10_2 Q2.hinj109_10_2
      Q2.hcardT109_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_10_2 i) (Q2.hfix109_10_2 i) _)
      colCert_109_10_1.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T109_10
      hfix109_10 hinj109_10 hcardT109_10
      (fun i => conj_mem_of_fixedPoints _ _ (T109_10 i) (hfix109_10 i) _)
      ⟨109, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T109_10_2 Q2.hfix109_10_2 Q2.hinj109_10_2
      Q2.hcardT109_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_10_2 i) (Q2.hfix109_10_2 i) _)
      colCert_109_10_2.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T109_10
      hfix109_10 hinj109_10 hcardT109_10
      (fun i => conj_mem_of_fixedPoints _ _ (T109_10 i) (hfix109_10 i) _)
      ⟨109, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T109_10_2 Q2.hfix109_10_2 Q2.hinj109_10_2
      Q2.hcardT109_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_10_2 i) (Q2.hfix109_10_2 i) _)
      colCert_109_10_3.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T109_10
      hfix109_10 hinj109_10 hcardT109_10
      (fun i => conj_mem_of_fixedPoints _ _ (T109_10 i) (hfix109_10 i) _)
      ⟨109, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T109_10_2 Q2.hfix109_10_2 Q2.hinj109_10_2
      Q2.hcardT109_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_10_2 i) (Q2.hfix109_10_2 i) _)
      colCert_109_10_4.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T109_12
      hfix109_12 hinj109_12 hcardT109_12
      (fun i => conj_mem_of_fixedPoints _ _ (T109_12 i) (hfix109_12 i) _)
      ⟨109, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T109_12_2 Q2.hfix109_12_2 Q2.hinj109_12_2
      Q2.hcardT109_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_12_2 i) (Q2.hfix109_12_2 i) _)
      colCert_109_12_0.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T109_12
      hfix109_12 hinj109_12 hcardT109_12
      (fun i => conj_mem_of_fixedPoints _ _ (T109_12 i) (hfix109_12 i) _)
      ⟨109, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T109_12_2 Q2.hfix109_12_2 Q2.hinj109_12_2
      Q2.hcardT109_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_12_2 i) (Q2.hfix109_12_2 i) _)
      colCert_109_12_1.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T109_12
      hfix109_12 hinj109_12 hcardT109_12
      (fun i => conj_mem_of_fixedPoints _ _ (T109_12 i) (hfix109_12 i) _)
      ⟨109, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T109_12_2 Q2.hfix109_12_2 Q2.hinj109_12_2
      Q2.hcardT109_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_12_2 i) (Q2.hfix109_12_2 i) _)
      colCert_109_12_2.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T109_12
      hfix109_12 hinj109_12 hcardT109_12
      (fun i => conj_mem_of_fixedPoints _ _ (T109_12 i) (hfix109_12 i) _)
      ⟨109, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T109_12_2 Q2.hfix109_12_2 Q2.hinj109_12_2
      Q2.hcardT109_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_12_2 i) (Q2.hfix109_12_2 i) _)
      colCert_109_12_3.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T109_12
      hfix109_12 hinj109_12 hcardT109_12
      (fun i => conj_mem_of_fixedPoints _ _ (T109_12 i) (hfix109_12 i) _)
      ⟨109, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T109_12_2 Q2.hfix109_12_2 Q2.hinj109_12_2
      Q2.hcardT109_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_12_2 i) (Q2.hfix109_12_2 i) _)
      colCert_109_12_4.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T109_47
      hfix109_47 hinj109_47 hcardT109_47
      (fun i => conj_mem_of_fixedPoints _ _ (T109_47 i) (hfix109_47 i) _)
      ⟨109, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T109_47_2 Q2.hfix109_47_2 Q2.hinj109_47_2
      Q2.hcardT109_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_47_2 i) (Q2.hfix109_47_2 i) _)
      colCert_109_47_0.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T109_47
      hfix109_47 hinj109_47 hcardT109_47
      (fun i => conj_mem_of_fixedPoints _ _ (T109_47 i) (hfix109_47 i) _)
      ⟨109, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T109_47_2 Q2.hfix109_47_2 Q2.hinj109_47_2
      Q2.hcardT109_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_47_2 i) (Q2.hfix109_47_2 i) _)
      colCert_109_47_1.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T109_47
      hfix109_47 hinj109_47 hcardT109_47
      (fun i => conj_mem_of_fixedPoints _ _ (T109_47 i) (hfix109_47 i) _)
      ⟨109, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T109_47_2 Q2.hfix109_47_2 Q2.hinj109_47_2
      Q2.hcardT109_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_47_2 i) (Q2.hfix109_47_2 i) _)
      colCert_109_47_2.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T109_47
      hfix109_47 hinj109_47 hcardT109_47
      (fun i => conj_mem_of_fixedPoints _ _ (T109_47 i) (hfix109_47 i) _)
      ⟨109, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T109_47_2 Q2.hfix109_47_2 Q2.hinj109_47_2
      Q2.hcardT109_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_47_2 i) (Q2.hfix109_47_2 i) _)
      colCert_109_47_3.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T109_47
      hfix109_47 hinj109_47 hcardT109_47
      (fun i => conj_mem_of_fixedPoints _ _ (T109_47 i) (hfix109_47 i) _)
      ⟨109, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T109_47_2 Q2.hfix109_47_2 Q2.hinj109_47_2
      Q2.hcardT109_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_47_2 i) (Q2.hfix109_47_2 i) _)
      colCert_109_47_4.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨109, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T109_47
      hfix109_47 hinj109_47 hcardT109_47
      (fun i => conj_mem_of_fixedPoints _ _ (T109_47 i) (hfix109_47 i) _)
      ⟨109, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T109_47_2 Q2.hfix109_47_2 Q2.hinj109_47_2
      Q2.hcardT109_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_47_2 i) (Q2.hfix109_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨109, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T109_47 = colFn colCertDiv_109_47_5.D1 (m := 25) from colCertDiv_109_47_5.bind1,
    show colData2 (⟨109, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T109_47_2 = colFn colCertDiv_109_47_5.D2 (m := 25) from colCertDiv_109_47_5.bind2]
  rw [alnId_109 j hj]
  exact fastcode_of_div ⟨109, by decide⟩ _ _ _
    ((alnId_109 j hj) ▸ Q2.listedAt (⟨109, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨109, by decide⟩ : Fin 148) hj hq).1) colCertDiv_109_47_5_match


theorem leaf_109_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨109, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T109_47
      hfix109_47 hinj109_47 hcardT109_47
      (fun i => conj_mem_of_fixedPoints _ _ (T109_47 i) (hfix109_47 i) _)
      ⟨109, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T109_47_2 Q2.hfix109_47_2 Q2.hinj109_47_2
      Q2.hcardT109_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_47_2 i) (Q2.hfix109_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨109, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T109_47 = colFn colCertDiv_109_47_10.D1 (m := 25) from colCertDiv_109_47_10.bind1,
    show colData2 (⟨109, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T109_47_2 = colFn colCertDiv_109_47_10.D2 (m := 25) from colCertDiv_109_47_10.bind2]
  rw [alnId_109 j hj]
  exact fastcode_of_div ⟨109, by decide⟩ _ _ _
    ((alnId_109 j hj) ▸ Q2.listedAt (⟨109, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨109, by decide⟩ : Fin 148) hj hq).1) colCertDiv_109_47_10_match


theorem leaf_109_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨109, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T109_47
      hfix109_47 hinj109_47 hcardT109_47
      (fun i => conj_mem_of_fixedPoints _ _ (T109_47 i) (hfix109_47 i) _)
      ⟨109, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T109_47_2 Q2.hfix109_47_2 Q2.hinj109_47_2
      Q2.hcardT109_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_47_2 i) (Q2.hfix109_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨109, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T109_47 = colFn colCertDiv_109_47_15.D1 (m := 25) from colCertDiv_109_47_15.bind1,
    show colData2 (⟨109, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T109_47_2 = colFn colCertDiv_109_47_15.D2 (m := 25) from colCertDiv_109_47_15.bind2]
  rw [alnId_109 j hj]
  exact fastcode_of_div ⟨109, by decide⟩ _ _ _
    ((alnId_109 j hj) ▸ Q2.listedAt (⟨109, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨109, by decide⟩ : Fin 148) hj hq).1) colCertDiv_109_47_15_match


theorem leaf_109_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨109, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T109_47
      hfix109_47 hinj109_47 hcardT109_47
      (fun i => conj_mem_of_fixedPoints _ _ (T109_47 i) (hfix109_47 i) _)
      ⟨109, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T109_47_2 Q2.hfix109_47_2 Q2.hinj109_47_2
      Q2.hcardT109_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_47_2 i) (Q2.hfix109_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨109, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T109_47 = colFn colCertDiv_109_47_20.D1 (m := 25) from colCertDiv_109_47_20.bind1,
    show colData2 (⟨109, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T109_47_2 = colFn colCertDiv_109_47_20.D2 (m := 25) from colCertDiv_109_47_20.bind2]
  rw [alnId_109 j hj]
  exact fastcode_of_div ⟨109, by decide⟩ _ _ _
    ((alnId_109 j hj) ▸ Q2.listedAt (⟨109, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨109, by decide⟩ : Fin 148) hj hq).1) colCertDiv_109_47_20_match


theorem leaf_109_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T109_53
      hfix109_53 hinj109_53 hcardT109_53
      (fun i => conj_mem_of_fixedPoints _ _ (T109_53 i) (hfix109_53 i) _)
      ⟨109, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T109_53_2 Q2.hfix109_53_2 Q2.hinj109_53_2
      Q2.hcardT109_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_53_2 i) (Q2.hfix109_53_2 i) _)
      colCert_109_53_0.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T109_53
      hfix109_53 hinj109_53 hcardT109_53
      (fun i => conj_mem_of_fixedPoints _ _ (T109_53 i) (hfix109_53 i) _)
      ⟨109, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T109_53_2 Q2.hfix109_53_2 Q2.hinj109_53_2
      Q2.hcardT109_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_53_2 i) (Q2.hfix109_53_2 i) _)
      colCert_109_53_1.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T109_53
      hfix109_53 hinj109_53 hcardT109_53
      (fun i => conj_mem_of_fixedPoints _ _ (T109_53 i) (hfix109_53 i) _)
      ⟨109, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T109_53_2 Q2.hfix109_53_2 Q2.hinj109_53_2
      Q2.hcardT109_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_53_2 i) (Q2.hfix109_53_2 i) _)
      colCert_109_53_2.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T109_53
      hfix109_53 hinj109_53 hcardT109_53
      (fun i => conj_mem_of_fixedPoints _ _ (T109_53 i) (hfix109_53 i) _)
      ⟨109, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T109_53_2 Q2.hfix109_53_2 Q2.hinj109_53_2
      Q2.hcardT109_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_53_2 i) (Q2.hfix109_53_2 i) _)
      colCert_109_53_3.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T109_53
      hfix109_53 hinj109_53 hcardT109_53
      (fun i => conj_mem_of_fixedPoints _ _ (T109_53 i) (hfix109_53 i) _)
      ⟨109, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T109_53_2 Q2.hfix109_53_2 Q2.hinj109_53_2
      Q2.hcardT109_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_53_2 i) (Q2.hfix109_53_2 i) _)
      colCert_109_53_4.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T109_53
      hfix109_53 hinj109_53 hcardT109_53
      (fun i => conj_mem_of_fixedPoints _ _ (T109_53 i) (hfix109_53 i) _)
      ⟨109, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T109_53_2 Q2.hfix109_53_2 Q2.hinj109_53_2
      Q2.hcardT109_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_53_2 i) (Q2.hfix109_53_2 i) _)
      colCert_109_53_5.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T109_53
      hfix109_53 hinj109_53 hcardT109_53
      (fun i => conj_mem_of_fixedPoints _ _ (T109_53 i) (hfix109_53 i) _)
      ⟨109, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T109_53_2 Q2.hfix109_53_2 Q2.hinj109_53_2
      Q2.hcardT109_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_53_2 i) (Q2.hfix109_53_2 i) _)
      colCert_109_53_10.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T109_53
      hfix109_53 hinj109_53 hcardT109_53
      (fun i => conj_mem_of_fixedPoints _ _ (T109_53 i) (hfix109_53 i) _)
      ⟨109, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T109_53_2 Q2.hfix109_53_2 Q2.hinj109_53_2
      Q2.hcardT109_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_53_2 i) (Q2.hfix109_53_2 i) _)
      colCert_109_53_15.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T109_53
      hfix109_53 hinj109_53 hcardT109_53
      (fun i => conj_mem_of_fixedPoints _ _ (T109_53 i) (hfix109_53 i) _)
      ⟨109, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T109_53_2 Q2.hfix109_53_2 Q2.hinj109_53_2
      Q2.hcardT109_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_53_2 i) (Q2.hfix109_53_2 i) _)
      colCert_109_53_20.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_109_0 (hp : 0 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 0 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp)) T109_109
      hfix109_109 hinj109_109 hcardT109_109
      (fun i => conj_mem_of_fixedPoints _ _ (T109_109 i) (hfix109_109 i) _)
      ⟨109, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 0 hp) Q2.T109_109_2 Q2.hfix109_109_2 Q2.hinj109_109_2
      Q2.hcardT109_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_109_2 i) (Q2.hfix109_109_2 i) _)
      colCert_109_109_0.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_109_1 (hp : 1 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 1 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp)) T109_109
      hfix109_109 hinj109_109 hcardT109_109
      (fun i => conj_mem_of_fixedPoints _ _ (T109_109 i) (hfix109_109 i) _)
      ⟨109, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 1 hp) Q2.T109_109_2 Q2.hfix109_109_2 Q2.hinj109_109_2
      Q2.hcardT109_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_109_2 i) (Q2.hfix109_109_2 i) _)
      colCert_109_109_1.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_109_2 (hp : 2 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 2 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp)) T109_109
      hfix109_109 hinj109_109 hcardT109_109
      (fun i => conj_mem_of_fixedPoints _ _ (T109_109 i) (hfix109_109 i) _)
      ⟨109, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 2 hp) Q2.T109_109_2 Q2.hfix109_109_2 Q2.hinj109_109_2
      Q2.hcardT109_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_109_2 i) (Q2.hfix109_109_2 i) _)
      colCert_109_109_2.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_109_3 (hp : 3 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 3 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp)) T109_109
      hfix109_109 hinj109_109 hcardT109_109
      (fun i => conj_mem_of_fixedPoints _ _ (T109_109 i) (hfix109_109 i) _)
      ⟨109, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 3 hp) Q2.T109_109_2 Q2.hfix109_109_2 Q2.hinj109_109_2
      Q2.hcardT109_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_109_2 i) (Q2.hfix109_109_2 i) _)
      colCert_109_109_3.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_109_4 (hp : 4 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 4 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp)) T109_109
      hfix109_109 hinj109_109 hcardT109_109
      (fun i => conj_mem_of_fixedPoints _ _ (T109_109 i) (hfix109_109 i) _)
      ⟨109, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 4 hp) Q2.T109_109_2 Q2.hfix109_109_2 Q2.hinj109_109_2
      Q2.hcardT109_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_109_2 i) (Q2.hfix109_109_2 i) _)
      colCert_109_109_4.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_109_5 (hp : 5 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 5 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp)) T109_109
      hfix109_109 hinj109_109 hcardT109_109
      (fun i => conj_mem_of_fixedPoints _ _ (T109_109 i) (hfix109_109 i) _)
      ⟨109, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 5 hp) Q2.T109_109_2 Q2.hfix109_109_2 Q2.hinj109_109_2
      Q2.hcardT109_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_109_2 i) (Q2.hfix109_109_2 i) _)
      colCert_109_109_5.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_109_10 (hp : 10 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 10 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp)) T109_109
      hfix109_109 hinj109_109 hcardT109_109
      (fun i => conj_mem_of_fixedPoints _ _ (T109_109 i) (hfix109_109 i) _)
      ⟨109, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 10 hp) Q2.T109_109_2 Q2.hfix109_109_2 Q2.hinj109_109_2
      Q2.hcardT109_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_109_2 i) (Q2.hfix109_109_2 i) _)
      colCert_109_109_10.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_109_15 (hp : 15 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 15 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp)) T109_109
      hfix109_109 hinj109_109 hcardT109_109
      (fun i => conj_mem_of_fixedPoints _ _ (T109_109 i) (hfix109_109 i) _)
      ⟨109, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 15 hp) Q2.T109_109_2 Q2.hfix109_109_2 Q2.hinj109_109_2
      Q2.hcardT109_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_109_2 i) (Q2.hfix109_109_2 i) _)
      colCert_109_109_15.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_109_109_20 (hp : 20 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 109 []).length)
    (hq : (normIsRep.getD 109 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 20 hp)
        (rowE2 (⟨109, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp))
        (rowE1 (⟨109, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨109, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨109, by decide⟩ (listedAt ⟨109, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp)) T109_109
      hfix109_109 hinj109_109 hcardT109_109
      (fun i => conj_mem_of_fixedPoints _ _ (T109_109 i) (hfix109_109 i) _)
      ⟨109, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨109, by decide⟩ (Q2.listedAt ⟨109, by decide⟩
        (alnCheck_rep ⟨109, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 20 hp) Q2.T109_109_2 Q2.hfix109_109_2 Q2.hinj109_109_2
      Q2.hcardT109_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T109_109_2 i) (Q2.hfix109_109_2 i) _)
      colCert_109_109_20.hD ?_).symm
  rw [alnId_109 j hj]


theorem leaf_110_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T110_10
      hfix110_10 hinj110_10 hcardT110_10
      (fun i => conj_mem_of_fixedPoints _ _ (T110_10 i) (hfix110_10 i) _)
      ⟨110, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T110_10_2 Q2.hfix110_10_2 Q2.hinj110_10_2
      Q2.hcardT110_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_10_2 i) (Q2.hfix110_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T110_10 = colFn colCert_110_10_0.D (m := 25) from colCert_110_10_0.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 0 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T110_10_2 = colFn colCert_110_10_0.D (m := 25) from colCert_110_10_0.bind2]
  exact alnAll_110_10_0 j hj hq

theorem leaf_110_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T110_10
      hfix110_10 hinj110_10 hcardT110_10
      (fun i => conj_mem_of_fixedPoints _ _ (T110_10 i) (hfix110_10 i) _)
      ⟨110, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T110_10_2 Q2.hfix110_10_2 Q2.hinj110_10_2
      Q2.hcardT110_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_10_2 i) (Q2.hfix110_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T110_10 = colFn colCert_110_10_1.D (m := 25) from colCert_110_10_1.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 1 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T110_10_2 = colFn colCert_110_10_1.D (m := 25) from colCert_110_10_1.bind2]
  exact alnAll_110_10_1 j hj hq

theorem leaf_110_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T110_10
      hfix110_10 hinj110_10 hcardT110_10
      (fun i => conj_mem_of_fixedPoints _ _ (T110_10 i) (hfix110_10 i) _)
      ⟨110, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T110_10_2 Q2.hfix110_10_2 Q2.hinj110_10_2
      Q2.hcardT110_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_10_2 i) (Q2.hfix110_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T110_10 = colFn colCert_110_10_2.D (m := 25) from colCert_110_10_2.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 2 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T110_10_2 = colFn colCert_110_10_2.D (m := 25) from colCert_110_10_2.bind2]
  exact alnAll_110_10_2 j hj hq

theorem leaf_110_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T110_10
      hfix110_10 hinj110_10 hcardT110_10
      (fun i => conj_mem_of_fixedPoints _ _ (T110_10 i) (hfix110_10 i) _)
      ⟨110, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T110_10_2 Q2.hfix110_10_2 Q2.hinj110_10_2
      Q2.hcardT110_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_10_2 i) (Q2.hfix110_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T110_10 = colFn colCert_110_10_3.D (m := 25) from colCert_110_10_3.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 3 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T110_10_2 = colFn colCert_110_10_3.D (m := 25) from colCert_110_10_3.bind2]
  exact alnAll_110_10_3 j hj hq

theorem leaf_110_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T110_10
      hfix110_10 hinj110_10 hcardT110_10
      (fun i => conj_mem_of_fixedPoints _ _ (T110_10 i) (hfix110_10 i) _)
      ⟨110, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T110_10_2 Q2.hfix110_10_2 Q2.hinj110_10_2
      Q2.hcardT110_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_10_2 i) (Q2.hfix110_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T110_10 = colFn colCert_110_10_4.D (m := 25) from colCert_110_10_4.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 4 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T110_10_2 = colFn colCert_110_10_4.D (m := 25) from colCert_110_10_4.bind2]
  exact alnAll_110_10_4 j hj hq

theorem leaf_110_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T110_12
      hfix110_12 hinj110_12 hcardT110_12
      (fun i => conj_mem_of_fixedPoints _ _ (T110_12 i) (hfix110_12 i) _)
      ⟨110, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T110_12_2 Q2.hfix110_12_2 Q2.hinj110_12_2
      Q2.hcardT110_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_12_2 i) (Q2.hfix110_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T110_12 = colFn colCert_110_12_0.D (m := 25) from colCert_110_12_0.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T110_12_2 = colFn colCert_110_12_0.D (m := 25) from colCert_110_12_0.bind2]
  exact alnAll_110_12_0 j hj hq

theorem leaf_110_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T110_12
      hfix110_12 hinj110_12 hcardT110_12
      (fun i => conj_mem_of_fixedPoints _ _ (T110_12 i) (hfix110_12 i) _)
      ⟨110, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T110_12_2 Q2.hfix110_12_2 Q2.hinj110_12_2
      Q2.hcardT110_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_12_2 i) (Q2.hfix110_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T110_12 = colFn colCert_110_12_1.D (m := 25) from colCert_110_12_1.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T110_12_2 = colFn colCert_110_12_1.D (m := 25) from colCert_110_12_1.bind2]
  exact alnAll_110_12_1 j hj hq

theorem leaf_110_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T110_12
      hfix110_12 hinj110_12 hcardT110_12
      (fun i => conj_mem_of_fixedPoints _ _ (T110_12 i) (hfix110_12 i) _)
      ⟨110, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T110_12_2 Q2.hfix110_12_2 Q2.hinj110_12_2
      Q2.hcardT110_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_12_2 i) (Q2.hfix110_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T110_12 = colFn colCert_110_12_2.D (m := 25) from colCert_110_12_2.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T110_12_2 = colFn colCert_110_12_2.D (m := 25) from colCert_110_12_2.bind2]
  exact alnAll_110_12_2 j hj hq

theorem leaf_110_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T110_12
      hfix110_12 hinj110_12 hcardT110_12
      (fun i => conj_mem_of_fixedPoints _ _ (T110_12 i) (hfix110_12 i) _)
      ⟨110, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T110_12_2 Q2.hfix110_12_2 Q2.hinj110_12_2
      Q2.hcardT110_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_12_2 i) (Q2.hfix110_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T110_12 = colFn colCert_110_12_3.D (m := 25) from colCert_110_12_3.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T110_12_2 = colFn colCert_110_12_3.D (m := 25) from colCert_110_12_3.bind2]
  exact alnAll_110_12_3 j hj hq

theorem leaf_110_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T110_12
      hfix110_12 hinj110_12 hcardT110_12
      (fun i => conj_mem_of_fixedPoints _ _ (T110_12 i) (hfix110_12 i) _)
      ⟨110, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T110_12_2 Q2.hfix110_12_2 Q2.hinj110_12_2
      Q2.hcardT110_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_12_2 i) (Q2.hfix110_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T110_12 = colFn colCert_110_12_4.D (m := 25) from colCert_110_12_4.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T110_12_2 = colFn colCert_110_12_4.D (m := 25) from colCert_110_12_4.bind2]
  exact alnAll_110_12_4 j hj hq

theorem leaf_110_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T110_48
      hfix110_48 hinj110_48 hcardT110_48
      (fun i => conj_mem_of_fixedPoints _ _ (T110_48 i) (hfix110_48 i) _)
      ⟨110, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T110_48_2 Q2.hfix110_48_2 Q2.hinj110_48_2
      Q2.hcardT110_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_48_2 i) (Q2.hfix110_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T110_48 = colFn colCert_110_48_0.D (m := 25) from colCert_110_48_0.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 0 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T110_48_2 = colFn colCert_110_48_0.D (m := 25) from colCert_110_48_0.bind2]
  exact alnAll_110_48_0 j hj hq

theorem leaf_110_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T110_48
      hfix110_48 hinj110_48 hcardT110_48
      (fun i => conj_mem_of_fixedPoints _ _ (T110_48 i) (hfix110_48 i) _)
      ⟨110, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T110_48_2 Q2.hfix110_48_2 Q2.hinj110_48_2
      Q2.hcardT110_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_48_2 i) (Q2.hfix110_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T110_48 = colFn colCert_110_48_1.D (m := 25) from colCert_110_48_1.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 1 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T110_48_2 = colFn colCert_110_48_1.D (m := 25) from colCert_110_48_1.bind2]
  exact alnAll_110_48_1 j hj hq

theorem leaf_110_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T110_48
      hfix110_48 hinj110_48 hcardT110_48
      (fun i => conj_mem_of_fixedPoints _ _ (T110_48 i) (hfix110_48 i) _)
      ⟨110, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T110_48_2 Q2.hfix110_48_2 Q2.hinj110_48_2
      Q2.hcardT110_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_48_2 i) (Q2.hfix110_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T110_48 = colFn colCert_110_48_2.D (m := 25) from colCert_110_48_2.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 2 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T110_48_2 = colFn colCert_110_48_2.D (m := 25) from colCert_110_48_2.bind2]
  exact alnAll_110_48_2 j hj hq

theorem leaf_110_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T110_48
      hfix110_48 hinj110_48 hcardT110_48
      (fun i => conj_mem_of_fixedPoints _ _ (T110_48 i) (hfix110_48 i) _)
      ⟨110, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T110_48_2 Q2.hfix110_48_2 Q2.hinj110_48_2
      Q2.hcardT110_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_48_2 i) (Q2.hfix110_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T110_48 = colFn colCert_110_48_3.D (m := 25) from colCert_110_48_3.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 3 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T110_48_2 = colFn colCert_110_48_3.D (m := 25) from colCert_110_48_3.bind2]
  exact alnAll_110_48_3 j hj hq

theorem leaf_110_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T110_48
      hfix110_48 hinj110_48 hcardT110_48
      (fun i => conj_mem_of_fixedPoints _ _ (T110_48 i) (hfix110_48 i) _)
      ⟨110, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T110_48_2 Q2.hfix110_48_2 Q2.hinj110_48_2
      Q2.hcardT110_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_48_2 i) (Q2.hfix110_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T110_48 = colFn colCert_110_48_4.D (m := 25) from colCert_110_48_4.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 4 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T110_48_2 = colFn colCert_110_48_4.D (m := 25) from colCert_110_48_4.bind2]
  exact alnAll_110_48_4 j hj hq

theorem leaf_110_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T110_48
      hfix110_48 hinj110_48 hcardT110_48
      (fun i => conj_mem_of_fixedPoints _ _ (T110_48 i) (hfix110_48 i) _)
      ⟨110, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T110_48_2 Q2.hfix110_48_2 Q2.hinj110_48_2
      Q2.hcardT110_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_48_2 i) (Q2.hfix110_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T110_48 = colFn colCertDiv_110_48_5.D1 (m := 25) from colCertDiv_110_48_5.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T110_48_2 = colFn colCertDiv_110_48_5.D2 (m := 25) from colCertDiv_110_48_5.bind2]
  exact alnAll_110_48_5 j hj hq

theorem leaf_110_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T110_48
      hfix110_48 hinj110_48 hcardT110_48
      (fun i => conj_mem_of_fixedPoints _ _ (T110_48 i) (hfix110_48 i) _)
      ⟨110, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T110_48_2 Q2.hfix110_48_2 Q2.hinj110_48_2
      Q2.hcardT110_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_48_2 i) (Q2.hfix110_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T110_48 = colFn colCertDiv_110_48_10.D1 (m := 25) from colCertDiv_110_48_10.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T110_48_2 = colFn colCertDiv_110_48_10.D2 (m := 25) from colCertDiv_110_48_10.bind2]
  exact alnAll_110_48_10 j hj hq

theorem leaf_110_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T110_48
      hfix110_48 hinj110_48 hcardT110_48
      (fun i => conj_mem_of_fixedPoints _ _ (T110_48 i) (hfix110_48 i) _)
      ⟨110, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T110_48_2 Q2.hfix110_48_2 Q2.hinj110_48_2
      Q2.hcardT110_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_48_2 i) (Q2.hfix110_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T110_48 = colFn colCertDiv_110_48_15.D1 (m := 25) from colCertDiv_110_48_15.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T110_48_2 = colFn colCertDiv_110_48_15.D2 (m := 25) from colCertDiv_110_48_15.bind2]
  exact alnAll_110_48_15 j hj hq

theorem leaf_110_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T110_48
      hfix110_48 hinj110_48 hcardT110_48
      (fun i => conj_mem_of_fixedPoints _ _ (T110_48 i) (hfix110_48 i) _)
      ⟨110, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T110_48_2 Q2.hfix110_48_2 Q2.hinj110_48_2
      Q2.hcardT110_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_48_2 i) (Q2.hfix110_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T110_48 = colFn colCertDiv_110_48_20.D1 (m := 25) from colCertDiv_110_48_20.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T110_48_2 = colFn colCertDiv_110_48_20.D2 (m := 25) from colCertDiv_110_48_20.bind2]
  exact alnAll_110_48_20 j hj hq

theorem leaf_110_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T110_53
      hfix110_53 hinj110_53 hcardT110_53
      (fun i => conj_mem_of_fixedPoints _ _ (T110_53 i) (hfix110_53 i) _)
      ⟨110, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T110_53_2 Q2.hfix110_53_2 Q2.hinj110_53_2
      Q2.hcardT110_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_53_2 i) (Q2.hfix110_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T110_53 = colFn colCert_110_53_0.D (m := 25) from colCert_110_53_0.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 0 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T110_53_2 = colFn colCert_110_53_0.D (m := 25) from colCert_110_53_0.bind2]
  exact alnAll_110_53_0 j hj hq

theorem leaf_110_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T110_53
      hfix110_53 hinj110_53 hcardT110_53
      (fun i => conj_mem_of_fixedPoints _ _ (T110_53 i) (hfix110_53 i) _)
      ⟨110, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T110_53_2 Q2.hfix110_53_2 Q2.hinj110_53_2
      Q2.hcardT110_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_53_2 i) (Q2.hfix110_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T110_53 = colFn colCert_110_53_1.D (m := 25) from colCert_110_53_1.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 1 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T110_53_2 = colFn colCert_110_53_1.D (m := 25) from colCert_110_53_1.bind2]
  exact alnAll_110_53_1 j hj hq

theorem leaf_110_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T110_53
      hfix110_53 hinj110_53 hcardT110_53
      (fun i => conj_mem_of_fixedPoints _ _ (T110_53 i) (hfix110_53 i) _)
      ⟨110, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T110_53_2 Q2.hfix110_53_2 Q2.hinj110_53_2
      Q2.hcardT110_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_53_2 i) (Q2.hfix110_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T110_53 = colFn colCert_110_53_2.D (m := 25) from colCert_110_53_2.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 2 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T110_53_2 = colFn colCert_110_53_2.D (m := 25) from colCert_110_53_2.bind2]
  exact alnAll_110_53_2 j hj hq

theorem leaf_110_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T110_53
      hfix110_53 hinj110_53 hcardT110_53
      (fun i => conj_mem_of_fixedPoints _ _ (T110_53 i) (hfix110_53 i) _)
      ⟨110, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T110_53_2 Q2.hfix110_53_2 Q2.hinj110_53_2
      Q2.hcardT110_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_53_2 i) (Q2.hfix110_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T110_53 = colFn colCert_110_53_3.D (m := 25) from colCert_110_53_3.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 3 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T110_53_2 = colFn colCert_110_53_3.D (m := 25) from colCert_110_53_3.bind2]
  exact alnAll_110_53_3 j hj hq

theorem leaf_110_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T110_53
      hfix110_53 hinj110_53 hcardT110_53
      (fun i => conj_mem_of_fixedPoints _ _ (T110_53 i) (hfix110_53 i) _)
      ⟨110, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T110_53_2 Q2.hfix110_53_2 Q2.hinj110_53_2
      Q2.hcardT110_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_53_2 i) (Q2.hfix110_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T110_53 = colFn colCert_110_53_4.D (m := 25) from colCert_110_53_4.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 4 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T110_53_2 = colFn colCert_110_53_4.D (m := 25) from colCert_110_53_4.bind2]
  exact alnAll_110_53_4 j hj hq

theorem leaf_110_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T110_53
      hfix110_53 hinj110_53 hcardT110_53
      (fun i => conj_mem_of_fixedPoints _ _ (T110_53 i) (hfix110_53 i) _)
      ⟨110, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T110_53_2 Q2.hfix110_53_2 Q2.hinj110_53_2
      Q2.hcardT110_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_53_2 i) (Q2.hfix110_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T110_53 = colFn colCert_110_53_5.D (m := 25) from colCert_110_53_5.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 5 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T110_53_2 = colFn colCert_110_53_5.D (m := 25) from colCert_110_53_5.bind2]
  exact alnAll_110_53_5 j hj hq

theorem leaf_110_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T110_53
      hfix110_53 hinj110_53 hcardT110_53
      (fun i => conj_mem_of_fixedPoints _ _ (T110_53 i) (hfix110_53 i) _)
      ⟨110, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T110_53_2 Q2.hfix110_53_2 Q2.hinj110_53_2
      Q2.hcardT110_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_53_2 i) (Q2.hfix110_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T110_53 = colFn colCert_110_53_10.D (m := 25) from colCert_110_53_10.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 10 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T110_53_2 = colFn colCert_110_53_10.D (m := 25) from colCert_110_53_10.bind2]
  exact alnAll_110_53_10 j hj hq

theorem leaf_110_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T110_53
      hfix110_53 hinj110_53 hcardT110_53
      (fun i => conj_mem_of_fixedPoints _ _ (T110_53 i) (hfix110_53 i) _)
      ⟨110, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T110_53_2 Q2.hfix110_53_2 Q2.hinj110_53_2
      Q2.hcardT110_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_53_2 i) (Q2.hfix110_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T110_53 = colFn colCert_110_53_15.D (m := 25) from colCert_110_53_15.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 15 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T110_53_2 = colFn colCert_110_53_15.D (m := 25) from colCert_110_53_15.bind2]
  exact alnAll_110_53_15 j hj hq

theorem leaf_110_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T110_53
      hfix110_53 hinj110_53 hcardT110_53
      (fun i => conj_mem_of_fixedPoints _ _ (T110_53 i) (hfix110_53 i) _)
      ⟨110, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T110_53_2 Q2.hfix110_53_2 Q2.hinj110_53_2
      Q2.hcardT110_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_53_2 i) (Q2.hfix110_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T110_53 = colFn colCert_110_53_20.D (m := 25) from colCert_110_53_20.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 20 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T110_53_2 = colFn colCert_110_53_20.D (m := 25) from colCert_110_53_20.bind2]
  exact alnAll_110_53_20 j hj hq

theorem leaf_110_110_0 (hp : 0 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 0 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 0 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 0 (transLenTr ⟨110, by decide⟩ 0 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_0.D (m := 25) from colCert_110_110_0.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 0 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_0.D (m := 25) from colCert_110_110_0.bind2]
  exact alnAll_110_110_0 j hj hq

theorem leaf_110_110_1 (hp : 1 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 1 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 1 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 1 (transLenTr ⟨110, by decide⟩ 1 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_1.D (m := 25) from colCert_110_110_1.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 1 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_1.D (m := 25) from colCert_110_110_1.bind2]
  exact alnAll_110_110_1 j hj hq

theorem leaf_110_110_2 (hp : 2 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 2 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 2 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 2 (transLenTr ⟨110, by decide⟩ 2 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_2.D (m := 25) from colCert_110_110_2.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 2 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_2.D (m := 25) from colCert_110_110_2.bind2]
  exact alnAll_110_110_2 j hj hq

theorem leaf_110_110_3 (hp : 3 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 3 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 3 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 3 (transLenTr ⟨110, by decide⟩ 3 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_3.D (m := 25) from colCert_110_110_3.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 3 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_3.D (m := 25) from colCert_110_110_3.bind2]
  exact alnAll_110_110_3 j hj hq

theorem leaf_110_110_4 (hp : 4 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 4 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 4 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 4 (transLenTr ⟨110, by decide⟩ 4 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_4.D (m := 25) from colCert_110_110_4.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 4 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_4.D (m := 25) from colCert_110_110_4.bind2]
  exact alnAll_110_110_4 j hj hq

theorem leaf_110_110_5 (hp : 5 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 5 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 5 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 5 (transLenTr ⟨110, by decide⟩ 5 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_5.D (m := 25) from colCert_110_110_5.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 5 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_5.D (m := 25) from colCert_110_110_5.bind2]
  exact alnAll_110_110_5 j hj hq

theorem leaf_110_110_10 (hp : 10 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 10 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 10 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 10 (transLenTr ⟨110, by decide⟩ 10 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_10.D (m := 25) from colCert_110_110_10.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 10 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_10.D (m := 25) from colCert_110_110_10.bind2]
  exact alnAll_110_110_10 j hj hq

theorem leaf_110_110_15 (hp : 15 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 15 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 15 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 15 (transLenTr ⟨110, by decide⟩ 15 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_15.D (m := 25) from colCert_110_110_15.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 15 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_15.D (m := 25) from colCert_110_110_15.bind2]
  exact alnAll_110_110_15 j hj hq

theorem leaf_110_110_20 (hp : 20 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 20 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 20 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 20 (transLenTr ⟨110, by decide⟩ 20 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_20.D (m := 25) from colCert_110_110_20.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 20 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_20.D (m := 25) from colCert_110_110_20.bind2]
  exact alnAll_110_110_20 j hj hq

theorem leaf_110_110_25 (hp : 25 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 25 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 25 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 25 (transLenTr ⟨110, by decide⟩ 25 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_25.D (m := 25) from colCert_110_110_25.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 25 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_25.D (m := 25) from colCert_110_110_25.bind2]
  exact alnAll_110_110_25 j hj hq

theorem leaf_110_110_50 (hp : 50 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 50 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 50 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 50 (transLenTr ⟨110, by decide⟩ 50 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_50.D (m := 25) from colCert_110_110_50.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 50 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_50.D (m := 25) from colCert_110_110_50.bind2]
  exact alnAll_110_110_50 j hj hq

theorem leaf_110_110_75 (hp : 75 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 75 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 75 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 75 (transLenTr ⟨110, by decide⟩ 75 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_75.D (m := 25) from colCert_110_110_75.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 75 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_75.D (m := 25) from colCert_110_110_75.bind2]
  exact alnAll_110_110_75 j hj hq

theorem leaf_110_110_100 (hp : 100 < (Q2.transData.getD 110 []).length)
    (j : Nat) (hj : j < (repChars.getD 110 []).length)
    (hq : (normIsRep.getD 110 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ 100 hp)
        (rowE2 (⟨110, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp))
        (rowE1 (⟨110, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨110, by decide⟩ : Fin 148) ⟨110, by decide⟩ _
      (validAt ⟨110, by decide⟩ (listedAt ⟨110, by decide⟩ hj))
      (colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp)) T110_110
      hfix110_110 hinj110_110 hcardT110_110
      (fun i => conj_mem_of_fixedPoints _ _ (T110_110 i) (hfix110_110 i) _)
      ⟨110, by decide⟩ ⟨110, by decide⟩ _
      (Q2.validAt ⟨110, by decide⟩ (Q2.listedAt ⟨110, by decide⟩
        (alnCheck_rep ⟨110, by decide⟩ hj hq).1))
      (colE2 ⟨110, by decide⟩ 100 hp) Q2.T110_110_2 Q2.hfix110_110_2 Q2.hinj110_110_2
      Q2.hcardT110_110_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T110_110_2 i) (Q2.hfix110_110_2 i) _)
      ?_).symm
  rw [show colData1 (⟨110, by decide⟩ : Fin 148)
        ((colE1 ⟨110, by decide⟩ 100 (transLenTr ⟨110, by decide⟩ 100 hp) : ↥(reps ⟨110, by decide⟩)) : Coordinate 1)
        T110_110 = colFn colCert_110_110_100.D (m := 25) from colCert_110_110_100.bind1,
    show colData2 (⟨110, by decide⟩ : Fin 148)
        ((colE2 ⟨110, by decide⟩ 100 hp : ↥(Q2.reps ⟨110, by decide⟩)) : Coordinate 2)
        Q2.T110_110_2 = colFn colCert_110_110_100.D (m := 25) from colCert_110_110_100.bind2]
  exact alnAll_110_110_100 j hj hq

theorem leaf_111_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T111_10
      hfix111_10 hinj111_10 hcardT111_10
      (fun i => conj_mem_of_fixedPoints _ _ (T111_10 i) (hfix111_10 i) _)
      ⟨111, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T111_10_2 Q2.hfix111_10_2 Q2.hinj111_10_2
      Q2.hcardT111_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_10_2 i) (Q2.hfix111_10_2 i) _)
      colCert_111_10_0.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T111_10
      hfix111_10 hinj111_10 hcardT111_10
      (fun i => conj_mem_of_fixedPoints _ _ (T111_10 i) (hfix111_10 i) _)
      ⟨111, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T111_10_2 Q2.hfix111_10_2 Q2.hinj111_10_2
      Q2.hcardT111_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_10_2 i) (Q2.hfix111_10_2 i) _)
      colCert_111_10_1.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T111_10
      hfix111_10 hinj111_10 hcardT111_10
      (fun i => conj_mem_of_fixedPoints _ _ (T111_10 i) (hfix111_10 i) _)
      ⟨111, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T111_10_2 Q2.hfix111_10_2 Q2.hinj111_10_2
      Q2.hcardT111_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_10_2 i) (Q2.hfix111_10_2 i) _)
      colCert_111_10_2.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T111_10
      hfix111_10 hinj111_10 hcardT111_10
      (fun i => conj_mem_of_fixedPoints _ _ (T111_10 i) (hfix111_10 i) _)
      ⟨111, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T111_10_2 Q2.hfix111_10_2 Q2.hinj111_10_2
      Q2.hcardT111_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_10_2 i) (Q2.hfix111_10_2 i) _)
      colCert_111_10_3.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T111_10
      hfix111_10 hinj111_10 hcardT111_10
      (fun i => conj_mem_of_fixedPoints _ _ (T111_10 i) (hfix111_10 i) _)
      ⟨111, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T111_10_2 Q2.hfix111_10_2 Q2.hinj111_10_2
      Q2.hcardT111_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_10_2 i) (Q2.hfix111_10_2 i) _)
      colCert_111_10_4.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T111_12
      hfix111_12 hinj111_12 hcardT111_12
      (fun i => conj_mem_of_fixedPoints _ _ (T111_12 i) (hfix111_12 i) _)
      ⟨111, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T111_12_2 Q2.hfix111_12_2 Q2.hinj111_12_2
      Q2.hcardT111_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_12_2 i) (Q2.hfix111_12_2 i) _)
      colCert_111_12_0.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T111_12
      hfix111_12 hinj111_12 hcardT111_12
      (fun i => conj_mem_of_fixedPoints _ _ (T111_12 i) (hfix111_12 i) _)
      ⟨111, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T111_12_2 Q2.hfix111_12_2 Q2.hinj111_12_2
      Q2.hcardT111_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_12_2 i) (Q2.hfix111_12_2 i) _)
      colCert_111_12_1.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T111_12
      hfix111_12 hinj111_12 hcardT111_12
      (fun i => conj_mem_of_fixedPoints _ _ (T111_12 i) (hfix111_12 i) _)
      ⟨111, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T111_12_2 Q2.hfix111_12_2 Q2.hinj111_12_2
      Q2.hcardT111_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_12_2 i) (Q2.hfix111_12_2 i) _)
      colCert_111_12_2.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T111_12
      hfix111_12 hinj111_12 hcardT111_12
      (fun i => conj_mem_of_fixedPoints _ _ (T111_12 i) (hfix111_12 i) _)
      ⟨111, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T111_12_2 Q2.hfix111_12_2 Q2.hinj111_12_2
      Q2.hcardT111_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_12_2 i) (Q2.hfix111_12_2 i) _)
      colCert_111_12_3.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T111_12
      hfix111_12 hinj111_12 hcardT111_12
      (fun i => conj_mem_of_fixedPoints _ _ (T111_12 i) (hfix111_12 i) _)
      ⟨111, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T111_12_2 Q2.hfix111_12_2 Q2.hinj111_12_2
      Q2.hcardT111_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_12_2 i) (Q2.hfix111_12_2 i) _)
      colCert_111_12_4.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T111_49
      hfix111_49 hinj111_49 hcardT111_49
      (fun i => conj_mem_of_fixedPoints _ _ (T111_49 i) (hfix111_49 i) _)
      ⟨111, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T111_49_2 Q2.hfix111_49_2 Q2.hinj111_49_2
      Q2.hcardT111_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_49_2 i) (Q2.hfix111_49_2 i) _)
      colCert_111_49_0.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T111_49
      hfix111_49 hinj111_49 hcardT111_49
      (fun i => conj_mem_of_fixedPoints _ _ (T111_49 i) (hfix111_49 i) _)
      ⟨111, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T111_49_2 Q2.hfix111_49_2 Q2.hinj111_49_2
      Q2.hcardT111_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_49_2 i) (Q2.hfix111_49_2 i) _)
      colCert_111_49_1.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T111_49
      hfix111_49 hinj111_49 hcardT111_49
      (fun i => conj_mem_of_fixedPoints _ _ (T111_49 i) (hfix111_49 i) _)
      ⟨111, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T111_49_2 Q2.hfix111_49_2 Q2.hinj111_49_2
      Q2.hcardT111_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_49_2 i) (Q2.hfix111_49_2 i) _)
      colCert_111_49_2.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T111_49
      hfix111_49 hinj111_49 hcardT111_49
      (fun i => conj_mem_of_fixedPoints _ _ (T111_49 i) (hfix111_49 i) _)
      ⟨111, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T111_49_2 Q2.hfix111_49_2 Q2.hinj111_49_2
      Q2.hcardT111_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_49_2 i) (Q2.hfix111_49_2 i) _)
      colCert_111_49_3.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T111_49
      hfix111_49 hinj111_49 hcardT111_49
      (fun i => conj_mem_of_fixedPoints _ _ (T111_49 i) (hfix111_49 i) _)
      ⟨111, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T111_49_2 Q2.hfix111_49_2 Q2.hinj111_49_2
      Q2.hcardT111_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_49_2 i) (Q2.hfix111_49_2 i) _)
      colCert_111_49_4.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T111_49
      hfix111_49 hinj111_49 hcardT111_49
      (fun i => conj_mem_of_fixedPoints _ _ (T111_49 i) (hfix111_49 i) _)
      ⟨111, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T111_49_2 Q2.hfix111_49_2 Q2.hinj111_49_2
      Q2.hcardT111_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_49_2 i) (Q2.hfix111_49_2 i) _)
      colCert_111_49_5.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T111_49
      hfix111_49 hinj111_49 hcardT111_49
      (fun i => conj_mem_of_fixedPoints _ _ (T111_49 i) (hfix111_49 i) _)
      ⟨111, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T111_49_2 Q2.hfix111_49_2 Q2.hinj111_49_2
      Q2.hcardT111_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_49_2 i) (Q2.hfix111_49_2 i) _)
      colCert_111_49_10.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T111_49
      hfix111_49 hinj111_49 hcardT111_49
      (fun i => conj_mem_of_fixedPoints _ _ (T111_49 i) (hfix111_49 i) _)
      ⟨111, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T111_49_2 Q2.hfix111_49_2 Q2.hinj111_49_2
      Q2.hcardT111_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_49_2 i) (Q2.hfix111_49_2 i) _)
      colCert_111_49_15.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T111_49
      hfix111_49 hinj111_49 hcardT111_49
      (fun i => conj_mem_of_fixedPoints _ _ (T111_49 i) (hfix111_49 i) _)
      ⟨111, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T111_49_2 Q2.hfix111_49_2 Q2.hinj111_49_2
      Q2.hcardT111_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_49_2 i) (Q2.hfix111_49_2 i) _)
      colCert_111_49_20.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T111_53
      hfix111_53 hinj111_53 hcardT111_53
      (fun i => conj_mem_of_fixedPoints _ _ (T111_53 i) (hfix111_53 i) _)
      ⟨111, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T111_53_2 Q2.hfix111_53_2 Q2.hinj111_53_2
      Q2.hcardT111_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_53_2 i) (Q2.hfix111_53_2 i) _)
      colCert_111_53_0.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T111_53
      hfix111_53 hinj111_53 hcardT111_53
      (fun i => conj_mem_of_fixedPoints _ _ (T111_53 i) (hfix111_53 i) _)
      ⟨111, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T111_53_2 Q2.hfix111_53_2 Q2.hinj111_53_2
      Q2.hcardT111_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_53_2 i) (Q2.hfix111_53_2 i) _)
      colCert_111_53_1.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T111_53
      hfix111_53 hinj111_53 hcardT111_53
      (fun i => conj_mem_of_fixedPoints _ _ (T111_53 i) (hfix111_53 i) _)
      ⟨111, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T111_53_2 Q2.hfix111_53_2 Q2.hinj111_53_2
      Q2.hcardT111_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_53_2 i) (Q2.hfix111_53_2 i) _)
      colCert_111_53_2.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T111_53
      hfix111_53 hinj111_53 hcardT111_53
      (fun i => conj_mem_of_fixedPoints _ _ (T111_53 i) (hfix111_53 i) _)
      ⟨111, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T111_53_2 Q2.hfix111_53_2 Q2.hinj111_53_2
      Q2.hcardT111_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_53_2 i) (Q2.hfix111_53_2 i) _)
      colCert_111_53_3.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T111_53
      hfix111_53 hinj111_53 hcardT111_53
      (fun i => conj_mem_of_fixedPoints _ _ (T111_53 i) (hfix111_53 i) _)
      ⟨111, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T111_53_2 Q2.hfix111_53_2 Q2.hinj111_53_2
      Q2.hcardT111_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_53_2 i) (Q2.hfix111_53_2 i) _)
      colCert_111_53_4.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T111_53
      hfix111_53 hinj111_53 hcardT111_53
      (fun i => conj_mem_of_fixedPoints _ _ (T111_53 i) (hfix111_53 i) _)
      ⟨111, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T111_53_2 Q2.hfix111_53_2 Q2.hinj111_53_2
      Q2.hcardT111_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_53_2 i) (Q2.hfix111_53_2 i) _)
      colCert_111_53_5.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T111_53
      hfix111_53 hinj111_53 hcardT111_53
      (fun i => conj_mem_of_fixedPoints _ _ (T111_53 i) (hfix111_53 i) _)
      ⟨111, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T111_53_2 Q2.hfix111_53_2 Q2.hinj111_53_2
      Q2.hcardT111_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_53_2 i) (Q2.hfix111_53_2 i) _)
      colCert_111_53_10.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T111_53
      hfix111_53 hinj111_53 hcardT111_53
      (fun i => conj_mem_of_fixedPoints _ _ (T111_53 i) (hfix111_53 i) _)
      ⟨111, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T111_53_2 Q2.hfix111_53_2 Q2.hinj111_53_2
      Q2.hcardT111_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_53_2 i) (Q2.hfix111_53_2 i) _)
      colCert_111_53_15.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T111_53
      hfix111_53 hinj111_53 hcardT111_53
      (fun i => conj_mem_of_fixedPoints _ _ (T111_53 i) (hfix111_53 i) _)
      ⟨111, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T111_53_2 Q2.hfix111_53_2 Q2.hinj111_53_2
      Q2.hcardT111_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_53_2 i) (Q2.hfix111_53_2 i) _)
      colCert_111_53_20.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_111_0 (hp : 0 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 0 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp)) T111_111
      hfix111_111 hinj111_111 hcardT111_111
      (fun i => conj_mem_of_fixedPoints _ _ (T111_111 i) (hfix111_111 i) _)
      ⟨111, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 0 hp) Q2.T111_111_2 Q2.hfix111_111_2 Q2.hinj111_111_2
      Q2.hcardT111_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_111_2 i) (Q2.hfix111_111_2 i) _)
      colCert_111_111_0.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_111_1 (hp : 1 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 1 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp)) T111_111
      hfix111_111 hinj111_111 hcardT111_111
      (fun i => conj_mem_of_fixedPoints _ _ (T111_111 i) (hfix111_111 i) _)
      ⟨111, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 1 hp) Q2.T111_111_2 Q2.hfix111_111_2 Q2.hinj111_111_2
      Q2.hcardT111_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_111_2 i) (Q2.hfix111_111_2 i) _)
      colCert_111_111_1.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_111_2 (hp : 2 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 2 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp)) T111_111
      hfix111_111 hinj111_111 hcardT111_111
      (fun i => conj_mem_of_fixedPoints _ _ (T111_111 i) (hfix111_111 i) _)
      ⟨111, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 2 hp) Q2.T111_111_2 Q2.hfix111_111_2 Q2.hinj111_111_2
      Q2.hcardT111_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_111_2 i) (Q2.hfix111_111_2 i) _)
      colCert_111_111_2.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_111_3 (hp : 3 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 3 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp)) T111_111
      hfix111_111 hinj111_111 hcardT111_111
      (fun i => conj_mem_of_fixedPoints _ _ (T111_111 i) (hfix111_111 i) _)
      ⟨111, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 3 hp) Q2.T111_111_2 Q2.hfix111_111_2 Q2.hinj111_111_2
      Q2.hcardT111_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_111_2 i) (Q2.hfix111_111_2 i) _)
      colCert_111_111_3.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_111_4 (hp : 4 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 4 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp)) T111_111
      hfix111_111 hinj111_111 hcardT111_111
      (fun i => conj_mem_of_fixedPoints _ _ (T111_111 i) (hfix111_111 i) _)
      ⟨111, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 4 hp) Q2.T111_111_2 Q2.hfix111_111_2 Q2.hinj111_111_2
      Q2.hcardT111_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_111_2 i) (Q2.hfix111_111_2 i) _)
      colCert_111_111_4.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_111_5 (hp : 5 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 5 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp)) T111_111
      hfix111_111 hinj111_111 hcardT111_111
      (fun i => conj_mem_of_fixedPoints _ _ (T111_111 i) (hfix111_111 i) _)
      ⟨111, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 5 hp) Q2.T111_111_2 Q2.hfix111_111_2 Q2.hinj111_111_2
      Q2.hcardT111_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_111_2 i) (Q2.hfix111_111_2 i) _)
      colCert_111_111_5.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_111_10 (hp : 10 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 10 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp)) T111_111
      hfix111_111 hinj111_111 hcardT111_111
      (fun i => conj_mem_of_fixedPoints _ _ (T111_111 i) (hfix111_111 i) _)
      ⟨111, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 10 hp) Q2.T111_111_2 Q2.hfix111_111_2 Q2.hinj111_111_2
      Q2.hcardT111_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_111_2 i) (Q2.hfix111_111_2 i) _)
      colCert_111_111_10.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_111_15 (hp : 15 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 15 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp)) T111_111
      hfix111_111 hinj111_111 hcardT111_111
      (fun i => conj_mem_of_fixedPoints _ _ (T111_111 i) (hfix111_111 i) _)
      ⟨111, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 15 hp) Q2.T111_111_2 Q2.hfix111_111_2 Q2.hinj111_111_2
      Q2.hcardT111_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_111_2 i) (Q2.hfix111_111_2 i) _)
      colCert_111_111_15.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_111_111_20 (hp : 20 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 111 []).length)
    (hq : (normIsRep.getD 111 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 20 hp)
        (rowE2 (⟨111, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp))
        (rowE1 (⟨111, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨111, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨111, by decide⟩ (listedAt ⟨111, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp)) T111_111
      hfix111_111 hinj111_111 hcardT111_111
      (fun i => conj_mem_of_fixedPoints _ _ (T111_111 i) (hfix111_111 i) _)
      ⟨111, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨111, by decide⟩ (Q2.listedAt ⟨111, by decide⟩
        (alnCheck_rep ⟨111, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 20 hp) Q2.T111_111_2 Q2.hfix111_111_2 Q2.hinj111_111_2
      Q2.hcardT111_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T111_111_2 i) (Q2.hfix111_111_2 i) _)
      colCert_111_111_20.hD ?_).symm
  rw [alnId_111 j hj]


theorem leaf_112_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T112_10
      hfix112_10 hinj112_10 hcardT112_10
      (fun i => conj_mem_of_fixedPoints _ _ (T112_10 i) (hfix112_10 i) _)
      ⟨112, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T112_10_2 Q2.hfix112_10_2 Q2.hinj112_10_2
      Q2.hcardT112_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_10_2 i) (Q2.hfix112_10_2 i) _)
      colCert_112_10_0.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T112_10
      hfix112_10 hinj112_10 hcardT112_10
      (fun i => conj_mem_of_fixedPoints _ _ (T112_10 i) (hfix112_10 i) _)
      ⟨112, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T112_10_2 Q2.hfix112_10_2 Q2.hinj112_10_2
      Q2.hcardT112_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_10_2 i) (Q2.hfix112_10_2 i) _)
      colCert_112_10_1.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T112_10
      hfix112_10 hinj112_10 hcardT112_10
      (fun i => conj_mem_of_fixedPoints _ _ (T112_10 i) (hfix112_10 i) _)
      ⟨112, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T112_10_2 Q2.hfix112_10_2 Q2.hinj112_10_2
      Q2.hcardT112_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_10_2 i) (Q2.hfix112_10_2 i) _)
      colCert_112_10_2.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T112_10
      hfix112_10 hinj112_10 hcardT112_10
      (fun i => conj_mem_of_fixedPoints _ _ (T112_10 i) (hfix112_10 i) _)
      ⟨112, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T112_10_2 Q2.hfix112_10_2 Q2.hinj112_10_2
      Q2.hcardT112_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_10_2 i) (Q2.hfix112_10_2 i) _)
      colCert_112_10_3.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T112_10
      hfix112_10 hinj112_10 hcardT112_10
      (fun i => conj_mem_of_fixedPoints _ _ (T112_10 i) (hfix112_10 i) _)
      ⟨112, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T112_10_2 Q2.hfix112_10_2 Q2.hinj112_10_2
      Q2.hcardT112_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_10_2 i) (Q2.hfix112_10_2 i) _)
      colCert_112_10_4.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T112_12
      hfix112_12 hinj112_12 hcardT112_12
      (fun i => conj_mem_of_fixedPoints _ _ (T112_12 i) (hfix112_12 i) _)
      ⟨112, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T112_12_2 Q2.hfix112_12_2 Q2.hinj112_12_2
      Q2.hcardT112_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_12_2 i) (Q2.hfix112_12_2 i) _)
      colCert_112_12_0.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T112_12
      hfix112_12 hinj112_12 hcardT112_12
      (fun i => conj_mem_of_fixedPoints _ _ (T112_12 i) (hfix112_12 i) _)
      ⟨112, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T112_12_2 Q2.hfix112_12_2 Q2.hinj112_12_2
      Q2.hcardT112_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_12_2 i) (Q2.hfix112_12_2 i) _)
      colCert_112_12_1.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T112_12
      hfix112_12 hinj112_12 hcardT112_12
      (fun i => conj_mem_of_fixedPoints _ _ (T112_12 i) (hfix112_12 i) _)
      ⟨112, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T112_12_2 Q2.hfix112_12_2 Q2.hinj112_12_2
      Q2.hcardT112_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_12_2 i) (Q2.hfix112_12_2 i) _)
      colCert_112_12_2.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T112_12
      hfix112_12 hinj112_12 hcardT112_12
      (fun i => conj_mem_of_fixedPoints _ _ (T112_12 i) (hfix112_12 i) _)
      ⟨112, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T112_12_2 Q2.hfix112_12_2 Q2.hinj112_12_2
      Q2.hcardT112_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_12_2 i) (Q2.hfix112_12_2 i) _)
      colCert_112_12_3.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T112_12
      hfix112_12 hinj112_12 hcardT112_12
      (fun i => conj_mem_of_fixedPoints _ _ (T112_12 i) (hfix112_12 i) _)
      ⟨112, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T112_12_2 Q2.hfix112_12_2 Q2.hinj112_12_2
      Q2.hcardT112_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_12_2 i) (Q2.hfix112_12_2 i) _)
      colCert_112_12_4.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T112_50
      hfix112_50 hinj112_50 hcardT112_50
      (fun i => conj_mem_of_fixedPoints _ _ (T112_50 i) (hfix112_50 i) _)
      ⟨112, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T112_50_2 Q2.hfix112_50_2 Q2.hinj112_50_2
      Q2.hcardT112_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_50_2 i) (Q2.hfix112_50_2 i) _)
      colCert_112_50_0.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T112_50
      hfix112_50 hinj112_50 hcardT112_50
      (fun i => conj_mem_of_fixedPoints _ _ (T112_50 i) (hfix112_50 i) _)
      ⟨112, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T112_50_2 Q2.hfix112_50_2 Q2.hinj112_50_2
      Q2.hcardT112_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_50_2 i) (Q2.hfix112_50_2 i) _)
      colCert_112_50_1.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T112_50
      hfix112_50 hinj112_50 hcardT112_50
      (fun i => conj_mem_of_fixedPoints _ _ (T112_50 i) (hfix112_50 i) _)
      ⟨112, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T112_50_2 Q2.hfix112_50_2 Q2.hinj112_50_2
      Q2.hcardT112_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_50_2 i) (Q2.hfix112_50_2 i) _)
      colCert_112_50_2.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T112_50
      hfix112_50 hinj112_50 hcardT112_50
      (fun i => conj_mem_of_fixedPoints _ _ (T112_50 i) (hfix112_50 i) _)
      ⟨112, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T112_50_2 Q2.hfix112_50_2 Q2.hinj112_50_2
      Q2.hcardT112_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_50_2 i) (Q2.hfix112_50_2 i) _)
      colCert_112_50_3.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T112_50
      hfix112_50 hinj112_50 hcardT112_50
      (fun i => conj_mem_of_fixedPoints _ _ (T112_50 i) (hfix112_50 i) _)
      ⟨112, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T112_50_2 Q2.hfix112_50_2 Q2.hinj112_50_2
      Q2.hcardT112_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_50_2 i) (Q2.hfix112_50_2 i) _)
      colCert_112_50_4.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨112, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T112_50
      hfix112_50 hinj112_50 hcardT112_50
      (fun i => conj_mem_of_fixedPoints _ _ (T112_50 i) (hfix112_50 i) _)
      ⟨112, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T112_50_2 Q2.hfix112_50_2 Q2.hinj112_50_2
      Q2.hcardT112_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_50_2 i) (Q2.hfix112_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨112, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T112_50 = colFn colCertDiv_112_50_5.D1 (m := 25) from colCertDiv_112_50_5.bind1,
    show colData2 (⟨112, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 5 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T112_50_2 = colFn colCertDiv_112_50_5.D2 (m := 25) from colCertDiv_112_50_5.bind2]
  rw [alnId_112 j hj]
  exact fastcode_of_div ⟨112, by decide⟩ _ _ _
    ((alnId_112 j hj) ▸ Q2.listedAt (⟨112, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨112, by decide⟩ : Fin 148) hj hq).1) colCertDiv_112_50_5_match


theorem leaf_112_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨112, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T112_50
      hfix112_50 hinj112_50 hcardT112_50
      (fun i => conj_mem_of_fixedPoints _ _ (T112_50 i) (hfix112_50 i) _)
      ⟨112, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T112_50_2 Q2.hfix112_50_2 Q2.hinj112_50_2
      Q2.hcardT112_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_50_2 i) (Q2.hfix112_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨112, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T112_50 = colFn colCertDiv_112_50_10.D1 (m := 25) from colCertDiv_112_50_10.bind1,
    show colData2 (⟨112, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 10 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T112_50_2 = colFn colCertDiv_112_50_10.D2 (m := 25) from colCertDiv_112_50_10.bind2]
  rw [alnId_112 j hj]
  exact fastcode_of_div ⟨112, by decide⟩ _ _ _
    ((alnId_112 j hj) ▸ Q2.listedAt (⟨112, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨112, by decide⟩ : Fin 148) hj hq).1) colCertDiv_112_50_10_match


theorem leaf_112_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨112, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T112_50
      hfix112_50 hinj112_50 hcardT112_50
      (fun i => conj_mem_of_fixedPoints _ _ (T112_50 i) (hfix112_50 i) _)
      ⟨112, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T112_50_2 Q2.hfix112_50_2 Q2.hinj112_50_2
      Q2.hcardT112_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_50_2 i) (Q2.hfix112_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨112, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T112_50 = colFn colCertDiv_112_50_15.D1 (m := 25) from colCertDiv_112_50_15.bind1,
    show colData2 (⟨112, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 15 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T112_50_2 = colFn colCertDiv_112_50_15.D2 (m := 25) from colCertDiv_112_50_15.bind2]
  rw [alnId_112 j hj]
  exact fastcode_of_div ⟨112, by decide⟩ _ _ _
    ((alnId_112 j hj) ▸ Q2.listedAt (⟨112, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨112, by decide⟩ : Fin 148) hj hq).1) colCertDiv_112_50_15_match


theorem leaf_112_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨112, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T112_50
      hfix112_50 hinj112_50 hcardT112_50
      (fun i => conj_mem_of_fixedPoints _ _ (T112_50 i) (hfix112_50 i) _)
      ⟨112, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T112_50_2 Q2.hfix112_50_2 Q2.hinj112_50_2
      Q2.hcardT112_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_50_2 i) (Q2.hfix112_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨112, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T112_50 = colFn colCertDiv_112_50_20.D1 (m := 25) from colCertDiv_112_50_20.bind1,
    show colData2 (⟨112, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 20 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T112_50_2 = colFn colCertDiv_112_50_20.D2 (m := 25) from colCertDiv_112_50_20.bind2]
  rw [alnId_112 j hj]
  exact fastcode_of_div ⟨112, by decide⟩ _ _ _
    ((alnId_112 j hj) ▸ Q2.listedAt (⟨112, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨112, by decide⟩ : Fin 148) hj hq).1) colCertDiv_112_50_20_match


theorem leaf_112_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T112_53
      hfix112_53 hinj112_53 hcardT112_53
      (fun i => conj_mem_of_fixedPoints _ _ (T112_53 i) (hfix112_53 i) _)
      ⟨112, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T112_53_2 Q2.hfix112_53_2 Q2.hinj112_53_2
      Q2.hcardT112_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_53_2 i) (Q2.hfix112_53_2 i) _)
      colCert_112_53_0.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T112_53
      hfix112_53 hinj112_53 hcardT112_53
      (fun i => conj_mem_of_fixedPoints _ _ (T112_53 i) (hfix112_53 i) _)
      ⟨112, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T112_53_2 Q2.hfix112_53_2 Q2.hinj112_53_2
      Q2.hcardT112_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_53_2 i) (Q2.hfix112_53_2 i) _)
      colCert_112_53_1.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T112_53
      hfix112_53 hinj112_53 hcardT112_53
      (fun i => conj_mem_of_fixedPoints _ _ (T112_53 i) (hfix112_53 i) _)
      ⟨112, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T112_53_2 Q2.hfix112_53_2 Q2.hinj112_53_2
      Q2.hcardT112_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_53_2 i) (Q2.hfix112_53_2 i) _)
      colCert_112_53_2.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T112_53
      hfix112_53 hinj112_53 hcardT112_53
      (fun i => conj_mem_of_fixedPoints _ _ (T112_53 i) (hfix112_53 i) _)
      ⟨112, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T112_53_2 Q2.hfix112_53_2 Q2.hinj112_53_2
      Q2.hcardT112_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_53_2 i) (Q2.hfix112_53_2 i) _)
      colCert_112_53_3.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T112_53
      hfix112_53 hinj112_53 hcardT112_53
      (fun i => conj_mem_of_fixedPoints _ _ (T112_53 i) (hfix112_53 i) _)
      ⟨112, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T112_53_2 Q2.hfix112_53_2 Q2.hinj112_53_2
      Q2.hcardT112_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_53_2 i) (Q2.hfix112_53_2 i) _)
      colCert_112_53_4.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T112_53
      hfix112_53 hinj112_53 hcardT112_53
      (fun i => conj_mem_of_fixedPoints _ _ (T112_53 i) (hfix112_53 i) _)
      ⟨112, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T112_53_2 Q2.hfix112_53_2 Q2.hinj112_53_2
      Q2.hcardT112_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_53_2 i) (Q2.hfix112_53_2 i) _)
      colCert_112_53_5.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T112_53
      hfix112_53 hinj112_53 hcardT112_53
      (fun i => conj_mem_of_fixedPoints _ _ (T112_53 i) (hfix112_53 i) _)
      ⟨112, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T112_53_2 Q2.hfix112_53_2 Q2.hinj112_53_2
      Q2.hcardT112_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_53_2 i) (Q2.hfix112_53_2 i) _)
      colCert_112_53_10.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T112_53
      hfix112_53 hinj112_53 hcardT112_53
      (fun i => conj_mem_of_fixedPoints _ _ (T112_53 i) (hfix112_53 i) _)
      ⟨112, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T112_53_2 Q2.hfix112_53_2 Q2.hinj112_53_2
      Q2.hcardT112_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_53_2 i) (Q2.hfix112_53_2 i) _)
      colCert_112_53_15.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T112_53
      hfix112_53 hinj112_53 hcardT112_53
      (fun i => conj_mem_of_fixedPoints _ _ (T112_53 i) (hfix112_53 i) _)
      ⟨112, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T112_53_2 Q2.hfix112_53_2 Q2.hinj112_53_2
      Q2.hcardT112_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_53_2 i) (Q2.hfix112_53_2 i) _)
      colCert_112_53_20.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_112_0 (hp : 0 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 0 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp)) T112_112
      hfix112_112 hinj112_112 hcardT112_112
      (fun i => conj_mem_of_fixedPoints _ _ (T112_112 i) (hfix112_112 i) _)
      ⟨112, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 0 hp) Q2.T112_112_2 Q2.hfix112_112_2 Q2.hinj112_112_2
      Q2.hcardT112_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_112_2 i) (Q2.hfix112_112_2 i) _)
      colCert_112_112_0.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_112_1 (hp : 1 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 1 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp)) T112_112
      hfix112_112 hinj112_112 hcardT112_112
      (fun i => conj_mem_of_fixedPoints _ _ (T112_112 i) (hfix112_112 i) _)
      ⟨112, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 1 hp) Q2.T112_112_2 Q2.hfix112_112_2 Q2.hinj112_112_2
      Q2.hcardT112_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_112_2 i) (Q2.hfix112_112_2 i) _)
      colCert_112_112_1.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_112_2 (hp : 2 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 2 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp)) T112_112
      hfix112_112 hinj112_112 hcardT112_112
      (fun i => conj_mem_of_fixedPoints _ _ (T112_112 i) (hfix112_112 i) _)
      ⟨112, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 2 hp) Q2.T112_112_2 Q2.hfix112_112_2 Q2.hinj112_112_2
      Q2.hcardT112_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_112_2 i) (Q2.hfix112_112_2 i) _)
      colCert_112_112_2.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_112_3 (hp : 3 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 3 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp)) T112_112
      hfix112_112 hinj112_112 hcardT112_112
      (fun i => conj_mem_of_fixedPoints _ _ (T112_112 i) (hfix112_112 i) _)
      ⟨112, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 3 hp) Q2.T112_112_2 Q2.hfix112_112_2 Q2.hinj112_112_2
      Q2.hcardT112_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_112_2 i) (Q2.hfix112_112_2 i) _)
      colCert_112_112_3.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_112_4 (hp : 4 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 4 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp)) T112_112
      hfix112_112 hinj112_112 hcardT112_112
      (fun i => conj_mem_of_fixedPoints _ _ (T112_112 i) (hfix112_112 i) _)
      ⟨112, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 4 hp) Q2.T112_112_2 Q2.hfix112_112_2 Q2.hinj112_112_2
      Q2.hcardT112_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_112_2 i) (Q2.hfix112_112_2 i) _)
      colCert_112_112_4.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_112_5 (hp : 5 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 5 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp)) T112_112
      hfix112_112 hinj112_112 hcardT112_112
      (fun i => conj_mem_of_fixedPoints _ _ (T112_112 i) (hfix112_112 i) _)
      ⟨112, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 5 hp) Q2.T112_112_2 Q2.hfix112_112_2 Q2.hinj112_112_2
      Q2.hcardT112_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_112_2 i) (Q2.hfix112_112_2 i) _)
      colCert_112_112_5.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_112_10 (hp : 10 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 10 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp)) T112_112
      hfix112_112 hinj112_112 hcardT112_112
      (fun i => conj_mem_of_fixedPoints _ _ (T112_112 i) (hfix112_112 i) _)
      ⟨112, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 10 hp) Q2.T112_112_2 Q2.hfix112_112_2 Q2.hinj112_112_2
      Q2.hcardT112_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_112_2 i) (Q2.hfix112_112_2 i) _)
      colCert_112_112_10.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_112_15 (hp : 15 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 15 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp)) T112_112
      hfix112_112 hinj112_112 hcardT112_112
      (fun i => conj_mem_of_fixedPoints _ _ (T112_112 i) (hfix112_112 i) _)
      ⟨112, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 15 hp) Q2.T112_112_2 Q2.hfix112_112_2 Q2.hinj112_112_2
      Q2.hcardT112_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_112_2 i) (Q2.hfix112_112_2 i) _)
      colCert_112_112_15.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_112_112_20 (hp : 20 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 112 []).length)
    (hq : (normIsRep.getD 112 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 20 hp)
        (rowE2 (⟨112, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp))
        (rowE1 (⟨112, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨112, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨112, by decide⟩ (listedAt ⟨112, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp)) T112_112
      hfix112_112 hinj112_112 hcardT112_112
      (fun i => conj_mem_of_fixedPoints _ _ (T112_112 i) (hfix112_112 i) _)
      ⟨112, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨112, by decide⟩ (Q2.listedAt ⟨112, by decide⟩
        (alnCheck_rep ⟨112, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 20 hp) Q2.T112_112_2 Q2.hfix112_112_2 Q2.hinj112_112_2
      Q2.hcardT112_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T112_112_2 i) (Q2.hfix112_112_2 i) _)
      colCert_112_112_20.hD ?_).symm
  rw [alnId_112 j hj]


theorem leaf_113_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T113_10
      hfix113_10 hinj113_10 hcardT113_10
      (fun i => conj_mem_of_fixedPoints _ _ (T113_10 i) (hfix113_10 i) _)
      ⟨113, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T113_10_2 Q2.hfix113_10_2 Q2.hinj113_10_2
      Q2.hcardT113_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_10_2 i) (Q2.hfix113_10_2 i) _)
      colCert_113_10_0.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T113_10
      hfix113_10 hinj113_10 hcardT113_10
      (fun i => conj_mem_of_fixedPoints _ _ (T113_10 i) (hfix113_10 i) _)
      ⟨113, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T113_10_2 Q2.hfix113_10_2 Q2.hinj113_10_2
      Q2.hcardT113_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_10_2 i) (Q2.hfix113_10_2 i) _)
      colCert_113_10_1.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T113_10
      hfix113_10 hinj113_10 hcardT113_10
      (fun i => conj_mem_of_fixedPoints _ _ (T113_10 i) (hfix113_10 i) _)
      ⟨113, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T113_10_2 Q2.hfix113_10_2 Q2.hinj113_10_2
      Q2.hcardT113_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_10_2 i) (Q2.hfix113_10_2 i) _)
      colCert_113_10_2.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T113_10
      hfix113_10 hinj113_10 hcardT113_10
      (fun i => conj_mem_of_fixedPoints _ _ (T113_10 i) (hfix113_10 i) _)
      ⟨113, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T113_10_2 Q2.hfix113_10_2 Q2.hinj113_10_2
      Q2.hcardT113_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_10_2 i) (Q2.hfix113_10_2 i) _)
      colCert_113_10_3.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T113_10
      hfix113_10 hinj113_10 hcardT113_10
      (fun i => conj_mem_of_fixedPoints _ _ (T113_10 i) (hfix113_10 i) _)
      ⟨113, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T113_10_2 Q2.hfix113_10_2 Q2.hinj113_10_2
      Q2.hcardT113_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_10_2 i) (Q2.hfix113_10_2 i) _)
      colCert_113_10_4.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T113_12
      hfix113_12 hinj113_12 hcardT113_12
      (fun i => conj_mem_of_fixedPoints _ _ (T113_12 i) (hfix113_12 i) _)
      ⟨113, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T113_12_2 Q2.hfix113_12_2 Q2.hinj113_12_2
      Q2.hcardT113_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_12_2 i) (Q2.hfix113_12_2 i) _)
      colCert_113_12_0.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T113_12
      hfix113_12 hinj113_12 hcardT113_12
      (fun i => conj_mem_of_fixedPoints _ _ (T113_12 i) (hfix113_12 i) _)
      ⟨113, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T113_12_2 Q2.hfix113_12_2 Q2.hinj113_12_2
      Q2.hcardT113_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_12_2 i) (Q2.hfix113_12_2 i) _)
      colCert_113_12_1.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T113_12
      hfix113_12 hinj113_12 hcardT113_12
      (fun i => conj_mem_of_fixedPoints _ _ (T113_12 i) (hfix113_12 i) _)
      ⟨113, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T113_12_2 Q2.hfix113_12_2 Q2.hinj113_12_2
      Q2.hcardT113_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_12_2 i) (Q2.hfix113_12_2 i) _)
      colCert_113_12_2.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T113_12
      hfix113_12 hinj113_12 hcardT113_12
      (fun i => conj_mem_of_fixedPoints _ _ (T113_12 i) (hfix113_12 i) _)
      ⟨113, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T113_12_2 Q2.hfix113_12_2 Q2.hinj113_12_2
      Q2.hcardT113_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_12_2 i) (Q2.hfix113_12_2 i) _)
      colCert_113_12_3.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T113_12
      hfix113_12 hinj113_12 hcardT113_12
      (fun i => conj_mem_of_fixedPoints _ _ (T113_12 i) (hfix113_12 i) _)
      ⟨113, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T113_12_2 Q2.hfix113_12_2 Q2.hinj113_12_2
      Q2.hcardT113_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_12_2 i) (Q2.hfix113_12_2 i) _)
      colCert_113_12_4.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T113_51
      hfix113_51 hinj113_51 hcardT113_51
      (fun i => conj_mem_of_fixedPoints _ _ (T113_51 i) (hfix113_51 i) _)
      ⟨113, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T113_51_2 Q2.hfix113_51_2 Q2.hinj113_51_2
      Q2.hcardT113_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_51_2 i) (Q2.hfix113_51_2 i) _)
      colCert_113_51_0.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T113_51
      hfix113_51 hinj113_51 hcardT113_51
      (fun i => conj_mem_of_fixedPoints _ _ (T113_51 i) (hfix113_51 i) _)
      ⟨113, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T113_51_2 Q2.hfix113_51_2 Q2.hinj113_51_2
      Q2.hcardT113_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_51_2 i) (Q2.hfix113_51_2 i) _)
      colCert_113_51_1.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T113_51
      hfix113_51 hinj113_51 hcardT113_51
      (fun i => conj_mem_of_fixedPoints _ _ (T113_51 i) (hfix113_51 i) _)
      ⟨113, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T113_51_2 Q2.hfix113_51_2 Q2.hinj113_51_2
      Q2.hcardT113_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_51_2 i) (Q2.hfix113_51_2 i) _)
      colCert_113_51_2.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T113_51
      hfix113_51 hinj113_51 hcardT113_51
      (fun i => conj_mem_of_fixedPoints _ _ (T113_51 i) (hfix113_51 i) _)
      ⟨113, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T113_51_2 Q2.hfix113_51_2 Q2.hinj113_51_2
      Q2.hcardT113_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_51_2 i) (Q2.hfix113_51_2 i) _)
      colCert_113_51_3.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T113_51
      hfix113_51 hinj113_51 hcardT113_51
      (fun i => conj_mem_of_fixedPoints _ _ (T113_51 i) (hfix113_51 i) _)
      ⟨113, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T113_51_2 Q2.hfix113_51_2 Q2.hinj113_51_2
      Q2.hcardT113_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_51_2 i) (Q2.hfix113_51_2 i) _)
      colCert_113_51_4.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨113, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T113_51
      hfix113_51 hinj113_51 hcardT113_51
      (fun i => conj_mem_of_fixedPoints _ _ (T113_51 i) (hfix113_51 i) _)
      ⟨113, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T113_51_2 Q2.hfix113_51_2 Q2.hinj113_51_2
      Q2.hcardT113_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_51_2 i) (Q2.hfix113_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨113, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T113_51 = colFn colCertDiv_113_51_5.D1 (m := 25) from colCertDiv_113_51_5.bind1,
    show colData2 (⟨113, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 5 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T113_51_2 = colFn colCertDiv_113_51_5.D2 (m := 25) from colCertDiv_113_51_5.bind2]
  rw [alnId_113 j hj]
  exact fastcode_of_div ⟨113, by decide⟩ _ _ _
    ((alnId_113 j hj) ▸ Q2.listedAt (⟨113, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨113, by decide⟩ : Fin 148) hj hq).1) colCertDiv_113_51_5_match


theorem leaf_113_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨113, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T113_51
      hfix113_51 hinj113_51 hcardT113_51
      (fun i => conj_mem_of_fixedPoints _ _ (T113_51 i) (hfix113_51 i) _)
      ⟨113, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T113_51_2 Q2.hfix113_51_2 Q2.hinj113_51_2
      Q2.hcardT113_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_51_2 i) (Q2.hfix113_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨113, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T113_51 = colFn colCertDiv_113_51_10.D1 (m := 25) from colCertDiv_113_51_10.bind1,
    show colData2 (⟨113, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 10 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T113_51_2 = colFn colCertDiv_113_51_10.D2 (m := 25) from colCertDiv_113_51_10.bind2]
  rw [alnId_113 j hj]
  exact fastcode_of_div ⟨113, by decide⟩ _ _ _
    ((alnId_113 j hj) ▸ Q2.listedAt (⟨113, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨113, by decide⟩ : Fin 148) hj hq).1) colCertDiv_113_51_10_match


theorem leaf_113_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨113, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T113_51
      hfix113_51 hinj113_51 hcardT113_51
      (fun i => conj_mem_of_fixedPoints _ _ (T113_51 i) (hfix113_51 i) _)
      ⟨113, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T113_51_2 Q2.hfix113_51_2 Q2.hinj113_51_2
      Q2.hcardT113_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_51_2 i) (Q2.hfix113_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨113, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T113_51 = colFn colCertDiv_113_51_15.D1 (m := 25) from colCertDiv_113_51_15.bind1,
    show colData2 (⟨113, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 15 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T113_51_2 = colFn colCertDiv_113_51_15.D2 (m := 25) from colCertDiv_113_51_15.bind2]
  rw [alnId_113 j hj]
  exact fastcode_of_div ⟨113, by decide⟩ _ _ _
    ((alnId_113 j hj) ▸ Q2.listedAt (⟨113, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨113, by decide⟩ : Fin 148) hj hq).1) colCertDiv_113_51_15_match


theorem leaf_113_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨113, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T113_51
      hfix113_51 hinj113_51 hcardT113_51
      (fun i => conj_mem_of_fixedPoints _ _ (T113_51 i) (hfix113_51 i) _)
      ⟨113, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T113_51_2 Q2.hfix113_51_2 Q2.hinj113_51_2
      Q2.hcardT113_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_51_2 i) (Q2.hfix113_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨113, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T113_51 = colFn colCertDiv_113_51_20.D1 (m := 25) from colCertDiv_113_51_20.bind1,
    show colData2 (⟨113, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 20 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T113_51_2 = colFn colCertDiv_113_51_20.D2 (m := 25) from colCertDiv_113_51_20.bind2]
  rw [alnId_113 j hj]
  exact fastcode_of_div ⟨113, by decide⟩ _ _ _
    ((alnId_113 j hj) ▸ Q2.listedAt (⟨113, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨113, by decide⟩ : Fin 148) hj hq).1) colCertDiv_113_51_20_match


theorem leaf_113_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T113_53
      hfix113_53 hinj113_53 hcardT113_53
      (fun i => conj_mem_of_fixedPoints _ _ (T113_53 i) (hfix113_53 i) _)
      ⟨113, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T113_53_2 Q2.hfix113_53_2 Q2.hinj113_53_2
      Q2.hcardT113_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_53_2 i) (Q2.hfix113_53_2 i) _)
      colCert_113_53_0.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T113_53
      hfix113_53 hinj113_53 hcardT113_53
      (fun i => conj_mem_of_fixedPoints _ _ (T113_53 i) (hfix113_53 i) _)
      ⟨113, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T113_53_2 Q2.hfix113_53_2 Q2.hinj113_53_2
      Q2.hcardT113_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_53_2 i) (Q2.hfix113_53_2 i) _)
      colCert_113_53_1.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T113_53
      hfix113_53 hinj113_53 hcardT113_53
      (fun i => conj_mem_of_fixedPoints _ _ (T113_53 i) (hfix113_53 i) _)
      ⟨113, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T113_53_2 Q2.hfix113_53_2 Q2.hinj113_53_2
      Q2.hcardT113_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_53_2 i) (Q2.hfix113_53_2 i) _)
      colCert_113_53_2.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T113_53
      hfix113_53 hinj113_53 hcardT113_53
      (fun i => conj_mem_of_fixedPoints _ _ (T113_53 i) (hfix113_53 i) _)
      ⟨113, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T113_53_2 Q2.hfix113_53_2 Q2.hinj113_53_2
      Q2.hcardT113_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_53_2 i) (Q2.hfix113_53_2 i) _)
      colCert_113_53_3.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T113_53
      hfix113_53 hinj113_53 hcardT113_53
      (fun i => conj_mem_of_fixedPoints _ _ (T113_53 i) (hfix113_53 i) _)
      ⟨113, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T113_53_2 Q2.hfix113_53_2 Q2.hinj113_53_2
      Q2.hcardT113_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_53_2 i) (Q2.hfix113_53_2 i) _)
      colCert_113_53_4.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T113_53
      hfix113_53 hinj113_53 hcardT113_53
      (fun i => conj_mem_of_fixedPoints _ _ (T113_53 i) (hfix113_53 i) _)
      ⟨113, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T113_53_2 Q2.hfix113_53_2 Q2.hinj113_53_2
      Q2.hcardT113_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_53_2 i) (Q2.hfix113_53_2 i) _)
      colCert_113_53_5.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T113_53
      hfix113_53 hinj113_53 hcardT113_53
      (fun i => conj_mem_of_fixedPoints _ _ (T113_53 i) (hfix113_53 i) _)
      ⟨113, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T113_53_2 Q2.hfix113_53_2 Q2.hinj113_53_2
      Q2.hcardT113_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_53_2 i) (Q2.hfix113_53_2 i) _)
      colCert_113_53_10.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T113_53
      hfix113_53 hinj113_53 hcardT113_53
      (fun i => conj_mem_of_fixedPoints _ _ (T113_53 i) (hfix113_53 i) _)
      ⟨113, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T113_53_2 Q2.hfix113_53_2 Q2.hinj113_53_2
      Q2.hcardT113_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_53_2 i) (Q2.hfix113_53_2 i) _)
      colCert_113_53_15.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T113_53
      hfix113_53 hinj113_53 hcardT113_53
      (fun i => conj_mem_of_fixedPoints _ _ (T113_53 i) (hfix113_53 i) _)
      ⟨113, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T113_53_2 Q2.hfix113_53_2 Q2.hinj113_53_2
      Q2.hcardT113_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_53_2 i) (Q2.hfix113_53_2 i) _)
      colCert_113_53_20.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_113_0 (hp : 0 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 0 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp)) T113_113
      hfix113_113 hinj113_113 hcardT113_113
      (fun i => conj_mem_of_fixedPoints _ _ (T113_113 i) (hfix113_113 i) _)
      ⟨113, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 0 hp) Q2.T113_113_2 Q2.hfix113_113_2 Q2.hinj113_113_2
      Q2.hcardT113_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_113_2 i) (Q2.hfix113_113_2 i) _)
      colCert_113_113_0.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_113_1 (hp : 1 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 1 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp)) T113_113
      hfix113_113 hinj113_113 hcardT113_113
      (fun i => conj_mem_of_fixedPoints _ _ (T113_113 i) (hfix113_113 i) _)
      ⟨113, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 1 hp) Q2.T113_113_2 Q2.hfix113_113_2 Q2.hinj113_113_2
      Q2.hcardT113_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_113_2 i) (Q2.hfix113_113_2 i) _)
      colCert_113_113_1.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_113_2 (hp : 2 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 2 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp)) T113_113
      hfix113_113 hinj113_113 hcardT113_113
      (fun i => conj_mem_of_fixedPoints _ _ (T113_113 i) (hfix113_113 i) _)
      ⟨113, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 2 hp) Q2.T113_113_2 Q2.hfix113_113_2 Q2.hinj113_113_2
      Q2.hcardT113_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_113_2 i) (Q2.hfix113_113_2 i) _)
      colCert_113_113_2.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_113_3 (hp : 3 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 3 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp)) T113_113
      hfix113_113 hinj113_113 hcardT113_113
      (fun i => conj_mem_of_fixedPoints _ _ (T113_113 i) (hfix113_113 i) _)
      ⟨113, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 3 hp) Q2.T113_113_2 Q2.hfix113_113_2 Q2.hinj113_113_2
      Q2.hcardT113_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_113_2 i) (Q2.hfix113_113_2 i) _)
      colCert_113_113_3.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_113_4 (hp : 4 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 4 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp)) T113_113
      hfix113_113 hinj113_113 hcardT113_113
      (fun i => conj_mem_of_fixedPoints _ _ (T113_113 i) (hfix113_113 i) _)
      ⟨113, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 4 hp) Q2.T113_113_2 Q2.hfix113_113_2 Q2.hinj113_113_2
      Q2.hcardT113_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_113_2 i) (Q2.hfix113_113_2 i) _)
      colCert_113_113_4.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_113_5 (hp : 5 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 5 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp)) T113_113
      hfix113_113 hinj113_113 hcardT113_113
      (fun i => conj_mem_of_fixedPoints _ _ (T113_113 i) (hfix113_113 i) _)
      ⟨113, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 5 hp) Q2.T113_113_2 Q2.hfix113_113_2 Q2.hinj113_113_2
      Q2.hcardT113_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_113_2 i) (Q2.hfix113_113_2 i) _)
      colCert_113_113_5.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_113_10 (hp : 10 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 10 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp)) T113_113
      hfix113_113 hinj113_113 hcardT113_113
      (fun i => conj_mem_of_fixedPoints _ _ (T113_113 i) (hfix113_113 i) _)
      ⟨113, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 10 hp) Q2.T113_113_2 Q2.hfix113_113_2 Q2.hinj113_113_2
      Q2.hcardT113_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_113_2 i) (Q2.hfix113_113_2 i) _)
      colCert_113_113_10.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_113_15 (hp : 15 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 15 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp)) T113_113
      hfix113_113 hinj113_113 hcardT113_113
      (fun i => conj_mem_of_fixedPoints _ _ (T113_113 i) (hfix113_113 i) _)
      ⟨113, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 15 hp) Q2.T113_113_2 Q2.hfix113_113_2 Q2.hinj113_113_2
      Q2.hcardT113_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_113_2 i) (Q2.hfix113_113_2 i) _)
      colCert_113_113_15.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_113_113_20 (hp : 20 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 113 []).length)
    (hq : (normIsRep.getD 113 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 20 hp)
        (rowE2 (⟨113, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp))
        (rowE1 (⟨113, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨113, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨113, by decide⟩ (listedAt ⟨113, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp)) T113_113
      hfix113_113 hinj113_113 hcardT113_113
      (fun i => conj_mem_of_fixedPoints _ _ (T113_113 i) (hfix113_113 i) _)
      ⟨113, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨113, by decide⟩ (Q2.listedAt ⟨113, by decide⟩
        (alnCheck_rep ⟨113, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 20 hp) Q2.T113_113_2 Q2.hfix113_113_2 Q2.hinj113_113_2
      Q2.hcardT113_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T113_113_2 i) (Q2.hfix113_113_2 i) _)
      colCert_113_113_20.hD ?_).symm
  rw [alnId_113 j hj]


theorem leaf_114_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T114_10
      hfix114_10 hinj114_10 hcardT114_10
      (fun i => conj_mem_of_fixedPoints _ _ (T114_10 i) (hfix114_10 i) _)
      ⟨114, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T114_10_2 Q2.hfix114_10_2 Q2.hinj114_10_2
      Q2.hcardT114_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_10_2 i) (Q2.hfix114_10_2 i) _)
      colCert_114_10_0.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T114_10
      hfix114_10 hinj114_10 hcardT114_10
      (fun i => conj_mem_of_fixedPoints _ _ (T114_10 i) (hfix114_10 i) _)
      ⟨114, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T114_10_2 Q2.hfix114_10_2 Q2.hinj114_10_2
      Q2.hcardT114_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_10_2 i) (Q2.hfix114_10_2 i) _)
      colCert_114_10_1.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T114_10
      hfix114_10 hinj114_10 hcardT114_10
      (fun i => conj_mem_of_fixedPoints _ _ (T114_10 i) (hfix114_10 i) _)
      ⟨114, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T114_10_2 Q2.hfix114_10_2 Q2.hinj114_10_2
      Q2.hcardT114_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_10_2 i) (Q2.hfix114_10_2 i) _)
      colCert_114_10_2.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T114_10
      hfix114_10 hinj114_10 hcardT114_10
      (fun i => conj_mem_of_fixedPoints _ _ (T114_10 i) (hfix114_10 i) _)
      ⟨114, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T114_10_2 Q2.hfix114_10_2 Q2.hinj114_10_2
      Q2.hcardT114_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_10_2 i) (Q2.hfix114_10_2 i) _)
      colCert_114_10_3.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T114_10
      hfix114_10 hinj114_10 hcardT114_10
      (fun i => conj_mem_of_fixedPoints _ _ (T114_10 i) (hfix114_10 i) _)
      ⟨114, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T114_10_2 Q2.hfix114_10_2 Q2.hinj114_10_2
      Q2.hcardT114_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_10_2 i) (Q2.hfix114_10_2 i) _)
      colCert_114_10_4.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T114_12
      hfix114_12 hinj114_12 hcardT114_12
      (fun i => conj_mem_of_fixedPoints _ _ (T114_12 i) (hfix114_12 i) _)
      ⟨114, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T114_12_2 Q2.hfix114_12_2 Q2.hinj114_12_2
      Q2.hcardT114_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_12_2 i) (Q2.hfix114_12_2 i) _)
      colCert_114_12_0.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T114_12
      hfix114_12 hinj114_12 hcardT114_12
      (fun i => conj_mem_of_fixedPoints _ _ (T114_12 i) (hfix114_12 i) _)
      ⟨114, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T114_12_2 Q2.hfix114_12_2 Q2.hinj114_12_2
      Q2.hcardT114_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_12_2 i) (Q2.hfix114_12_2 i) _)
      colCert_114_12_1.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T114_12
      hfix114_12 hinj114_12 hcardT114_12
      (fun i => conj_mem_of_fixedPoints _ _ (T114_12 i) (hfix114_12 i) _)
      ⟨114, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T114_12_2 Q2.hfix114_12_2 Q2.hinj114_12_2
      Q2.hcardT114_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_12_2 i) (Q2.hfix114_12_2 i) _)
      colCert_114_12_2.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T114_12
      hfix114_12 hinj114_12 hcardT114_12
      (fun i => conj_mem_of_fixedPoints _ _ (T114_12 i) (hfix114_12 i) _)
      ⟨114, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T114_12_2 Q2.hfix114_12_2 Q2.hinj114_12_2
      Q2.hcardT114_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_12_2 i) (Q2.hfix114_12_2 i) _)
      colCert_114_12_3.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T114_12
      hfix114_12 hinj114_12 hcardT114_12
      (fun i => conj_mem_of_fixedPoints _ _ (T114_12 i) (hfix114_12 i) _)
      ⟨114, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T114_12_2 Q2.hfix114_12_2 Q2.hinj114_12_2
      Q2.hcardT114_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_12_2 i) (Q2.hfix114_12_2 i) _)
      colCert_114_12_4.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T114_52
      hfix114_52 hinj114_52 hcardT114_52
      (fun i => conj_mem_of_fixedPoints _ _ (T114_52 i) (hfix114_52 i) _)
      ⟨114, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T114_52_2 Q2.hfix114_52_2 Q2.hinj114_52_2
      Q2.hcardT114_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_52_2 i) (Q2.hfix114_52_2 i) _)
      colCert_114_52_0.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T114_52
      hfix114_52 hinj114_52 hcardT114_52
      (fun i => conj_mem_of_fixedPoints _ _ (T114_52 i) (hfix114_52 i) _)
      ⟨114, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T114_52_2 Q2.hfix114_52_2 Q2.hinj114_52_2
      Q2.hcardT114_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_52_2 i) (Q2.hfix114_52_2 i) _)
      colCert_114_52_1.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T114_52
      hfix114_52 hinj114_52 hcardT114_52
      (fun i => conj_mem_of_fixedPoints _ _ (T114_52 i) (hfix114_52 i) _)
      ⟨114, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T114_52_2 Q2.hfix114_52_2 Q2.hinj114_52_2
      Q2.hcardT114_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_52_2 i) (Q2.hfix114_52_2 i) _)
      colCert_114_52_2.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T114_52
      hfix114_52 hinj114_52 hcardT114_52
      (fun i => conj_mem_of_fixedPoints _ _ (T114_52 i) (hfix114_52 i) _)
      ⟨114, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T114_52_2 Q2.hfix114_52_2 Q2.hinj114_52_2
      Q2.hcardT114_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_52_2 i) (Q2.hfix114_52_2 i) _)
      colCert_114_52_3.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T114_52
      hfix114_52 hinj114_52 hcardT114_52
      (fun i => conj_mem_of_fixedPoints _ _ (T114_52 i) (hfix114_52 i) _)
      ⟨114, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T114_52_2 Q2.hfix114_52_2 Q2.hinj114_52_2
      Q2.hcardT114_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_52_2 i) (Q2.hfix114_52_2 i) _)
      colCert_114_52_4.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨114, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T114_52
      hfix114_52 hinj114_52 hcardT114_52
      (fun i => conj_mem_of_fixedPoints _ _ (T114_52 i) (hfix114_52 i) _)
      ⟨114, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T114_52_2 Q2.hfix114_52_2 Q2.hinj114_52_2
      Q2.hcardT114_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_52_2 i) (Q2.hfix114_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨114, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T114_52 = colFn colCertDiv_114_52_5.D1 (m := 25) from colCertDiv_114_52_5.bind1,
    show colData2 (⟨114, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T114_52_2 = colFn colCertDiv_114_52_5.D2 (m := 25) from colCertDiv_114_52_5.bind2]
  rw [alnId_114 j hj]
  exact fastcode_of_div ⟨114, by decide⟩ _ _ _
    ((alnId_114 j hj) ▸ Q2.listedAt (⟨114, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨114, by decide⟩ : Fin 148) hj hq).1) colCertDiv_114_52_5_match


theorem leaf_114_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨114, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T114_52
      hfix114_52 hinj114_52 hcardT114_52
      (fun i => conj_mem_of_fixedPoints _ _ (T114_52 i) (hfix114_52 i) _)
      ⟨114, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T114_52_2 Q2.hfix114_52_2 Q2.hinj114_52_2
      Q2.hcardT114_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_52_2 i) (Q2.hfix114_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨114, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T114_52 = colFn colCertDiv_114_52_10.D1 (m := 25) from colCertDiv_114_52_10.bind1,
    show colData2 (⟨114, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T114_52_2 = colFn colCertDiv_114_52_10.D2 (m := 25) from colCertDiv_114_52_10.bind2]
  rw [alnId_114 j hj]
  exact fastcode_of_div ⟨114, by decide⟩ _ _ _
    ((alnId_114 j hj) ▸ Q2.listedAt (⟨114, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨114, by decide⟩ : Fin 148) hj hq).1) colCertDiv_114_52_10_match


theorem leaf_114_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨114, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T114_52
      hfix114_52 hinj114_52 hcardT114_52
      (fun i => conj_mem_of_fixedPoints _ _ (T114_52 i) (hfix114_52 i) _)
      ⟨114, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T114_52_2 Q2.hfix114_52_2 Q2.hinj114_52_2
      Q2.hcardT114_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_52_2 i) (Q2.hfix114_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨114, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T114_52 = colFn colCertDiv_114_52_15.D1 (m := 25) from colCertDiv_114_52_15.bind1,
    show colData2 (⟨114, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T114_52_2 = colFn colCertDiv_114_52_15.D2 (m := 25) from colCertDiv_114_52_15.bind2]
  rw [alnId_114 j hj]
  exact fastcode_of_div ⟨114, by decide⟩ _ _ _
    ((alnId_114 j hj) ▸ Q2.listedAt (⟨114, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨114, by decide⟩ : Fin 148) hj hq).1) colCertDiv_114_52_15_match


theorem leaf_114_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨114, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T114_52
      hfix114_52 hinj114_52 hcardT114_52
      (fun i => conj_mem_of_fixedPoints _ _ (T114_52 i) (hfix114_52 i) _)
      ⟨114, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T114_52_2 Q2.hfix114_52_2 Q2.hinj114_52_2
      Q2.hcardT114_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_52_2 i) (Q2.hfix114_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨114, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T114_52 = colFn colCertDiv_114_52_20.D1 (m := 25) from colCertDiv_114_52_20.bind1,
    show colData2 (⟨114, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T114_52_2 = colFn colCertDiv_114_52_20.D2 (m := 25) from colCertDiv_114_52_20.bind2]
  rw [alnId_114 j hj]
  exact fastcode_of_div ⟨114, by decide⟩ _ _ _
    ((alnId_114 j hj) ▸ Q2.listedAt (⟨114, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨114, by decide⟩ : Fin 148) hj hq).1) colCertDiv_114_52_20_match


theorem leaf_114_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T114_53
      hfix114_53 hinj114_53 hcardT114_53
      (fun i => conj_mem_of_fixedPoints _ _ (T114_53 i) (hfix114_53 i) _)
      ⟨114, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T114_53_2 Q2.hfix114_53_2 Q2.hinj114_53_2
      Q2.hcardT114_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_53_2 i) (Q2.hfix114_53_2 i) _)
      colCert_114_53_0.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T114_53
      hfix114_53 hinj114_53 hcardT114_53
      (fun i => conj_mem_of_fixedPoints _ _ (T114_53 i) (hfix114_53 i) _)
      ⟨114, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T114_53_2 Q2.hfix114_53_2 Q2.hinj114_53_2
      Q2.hcardT114_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_53_2 i) (Q2.hfix114_53_2 i) _)
      colCert_114_53_1.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T114_53
      hfix114_53 hinj114_53 hcardT114_53
      (fun i => conj_mem_of_fixedPoints _ _ (T114_53 i) (hfix114_53 i) _)
      ⟨114, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T114_53_2 Q2.hfix114_53_2 Q2.hinj114_53_2
      Q2.hcardT114_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_53_2 i) (Q2.hfix114_53_2 i) _)
      colCert_114_53_2.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T114_53
      hfix114_53 hinj114_53 hcardT114_53
      (fun i => conj_mem_of_fixedPoints _ _ (T114_53 i) (hfix114_53 i) _)
      ⟨114, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T114_53_2 Q2.hfix114_53_2 Q2.hinj114_53_2
      Q2.hcardT114_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_53_2 i) (Q2.hfix114_53_2 i) _)
      colCert_114_53_3.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T114_53
      hfix114_53 hinj114_53 hcardT114_53
      (fun i => conj_mem_of_fixedPoints _ _ (T114_53 i) (hfix114_53 i) _)
      ⟨114, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T114_53_2 Q2.hfix114_53_2 Q2.hinj114_53_2
      Q2.hcardT114_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_53_2 i) (Q2.hfix114_53_2 i) _)
      colCert_114_53_4.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T114_53
      hfix114_53 hinj114_53 hcardT114_53
      (fun i => conj_mem_of_fixedPoints _ _ (T114_53 i) (hfix114_53 i) _)
      ⟨114, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T114_53_2 Q2.hfix114_53_2 Q2.hinj114_53_2
      Q2.hcardT114_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_53_2 i) (Q2.hfix114_53_2 i) _)
      colCert_114_53_5.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T114_53
      hfix114_53 hinj114_53 hcardT114_53
      (fun i => conj_mem_of_fixedPoints _ _ (T114_53 i) (hfix114_53 i) _)
      ⟨114, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T114_53_2 Q2.hfix114_53_2 Q2.hinj114_53_2
      Q2.hcardT114_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_53_2 i) (Q2.hfix114_53_2 i) _)
      colCert_114_53_10.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T114_53
      hfix114_53 hinj114_53 hcardT114_53
      (fun i => conj_mem_of_fixedPoints _ _ (T114_53 i) (hfix114_53 i) _)
      ⟨114, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T114_53_2 Q2.hfix114_53_2 Q2.hinj114_53_2
      Q2.hcardT114_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_53_2 i) (Q2.hfix114_53_2 i) _)
      colCert_114_53_15.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T114_53
      hfix114_53 hinj114_53 hcardT114_53
      (fun i => conj_mem_of_fixedPoints _ _ (T114_53 i) (hfix114_53 i) _)
      ⟨114, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T114_53_2 Q2.hfix114_53_2 Q2.hinj114_53_2
      Q2.hcardT114_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_53_2 i) (Q2.hfix114_53_2 i) _)
      colCert_114_53_20.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_114_0 (hp : 0 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 0 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp)) T114_114
      hfix114_114 hinj114_114 hcardT114_114
      (fun i => conj_mem_of_fixedPoints _ _ (T114_114 i) (hfix114_114 i) _)
      ⟨114, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 0 hp) Q2.T114_114_2 Q2.hfix114_114_2 Q2.hinj114_114_2
      Q2.hcardT114_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_114_2 i) (Q2.hfix114_114_2 i) _)
      colCert_114_114_0.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_114_1 (hp : 1 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 1 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp)) T114_114
      hfix114_114 hinj114_114 hcardT114_114
      (fun i => conj_mem_of_fixedPoints _ _ (T114_114 i) (hfix114_114 i) _)
      ⟨114, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 1 hp) Q2.T114_114_2 Q2.hfix114_114_2 Q2.hinj114_114_2
      Q2.hcardT114_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_114_2 i) (Q2.hfix114_114_2 i) _)
      colCert_114_114_1.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_114_2 (hp : 2 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 2 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp)) T114_114
      hfix114_114 hinj114_114 hcardT114_114
      (fun i => conj_mem_of_fixedPoints _ _ (T114_114 i) (hfix114_114 i) _)
      ⟨114, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 2 hp) Q2.T114_114_2 Q2.hfix114_114_2 Q2.hinj114_114_2
      Q2.hcardT114_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_114_2 i) (Q2.hfix114_114_2 i) _)
      colCert_114_114_2.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_114_3 (hp : 3 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 3 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp)) T114_114
      hfix114_114 hinj114_114 hcardT114_114
      (fun i => conj_mem_of_fixedPoints _ _ (T114_114 i) (hfix114_114 i) _)
      ⟨114, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 3 hp) Q2.T114_114_2 Q2.hfix114_114_2 Q2.hinj114_114_2
      Q2.hcardT114_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_114_2 i) (Q2.hfix114_114_2 i) _)
      colCert_114_114_3.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_114_4 (hp : 4 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 4 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp)) T114_114
      hfix114_114 hinj114_114 hcardT114_114
      (fun i => conj_mem_of_fixedPoints _ _ (T114_114 i) (hfix114_114 i) _)
      ⟨114, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 4 hp) Q2.T114_114_2 Q2.hfix114_114_2 Q2.hinj114_114_2
      Q2.hcardT114_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_114_2 i) (Q2.hfix114_114_2 i) _)
      colCert_114_114_4.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_114_5 (hp : 5 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 5 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp)) T114_114
      hfix114_114 hinj114_114 hcardT114_114
      (fun i => conj_mem_of_fixedPoints _ _ (T114_114 i) (hfix114_114 i) _)
      ⟨114, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 5 hp) Q2.T114_114_2 Q2.hfix114_114_2 Q2.hinj114_114_2
      Q2.hcardT114_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_114_2 i) (Q2.hfix114_114_2 i) _)
      colCert_114_114_5.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_114_10 (hp : 10 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 10 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp)) T114_114
      hfix114_114 hinj114_114 hcardT114_114
      (fun i => conj_mem_of_fixedPoints _ _ (T114_114 i) (hfix114_114 i) _)
      ⟨114, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 10 hp) Q2.T114_114_2 Q2.hfix114_114_2 Q2.hinj114_114_2
      Q2.hcardT114_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_114_2 i) (Q2.hfix114_114_2 i) _)
      colCert_114_114_10.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_114_15 (hp : 15 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 15 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp)) T114_114
      hfix114_114 hinj114_114 hcardT114_114
      (fun i => conj_mem_of_fixedPoints _ _ (T114_114 i) (hfix114_114 i) _)
      ⟨114, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 15 hp) Q2.T114_114_2 Q2.hfix114_114_2 Q2.hinj114_114_2
      Q2.hcardT114_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_114_2 i) (Q2.hfix114_114_2 i) _)
      colCert_114_114_15.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_114_114_20 (hp : 20 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 114 []).length)
    (hq : (normIsRep.getD 114 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 20 hp)
        (rowE2 (⟨114, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp))
        (rowE1 (⟨114, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨114, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨114, by decide⟩ (listedAt ⟨114, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp)) T114_114
      hfix114_114 hinj114_114 hcardT114_114
      (fun i => conj_mem_of_fixedPoints _ _ (T114_114 i) (hfix114_114 i) _)
      ⟨114, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨114, by decide⟩ (Q2.listedAt ⟨114, by decide⟩
        (alnCheck_rep ⟨114, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 20 hp) Q2.T114_114_2 Q2.hfix114_114_2 Q2.hinj114_114_2
      Q2.hcardT114_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T114_114_2 i) (Q2.hfix114_114_2 i) _)
      colCert_114_114_20.hD ?_).symm
  rw [alnId_114 j hj]


theorem leaf_115_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T115_10
      hfix115_10 hinj115_10 hcardT115_10
      (fun i => conj_mem_of_fixedPoints _ _ (T115_10 i) (hfix115_10 i) _)
      ⟨115, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T115_10_2 Q2.hfix115_10_2 Q2.hinj115_10_2
      Q2.hcardT115_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_10_2 i) (Q2.hfix115_10_2 i) _)
      colCert_115_10_0.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T115_10
      hfix115_10 hinj115_10 hcardT115_10
      (fun i => conj_mem_of_fixedPoints _ _ (T115_10 i) (hfix115_10 i) _)
      ⟨115, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T115_10_2 Q2.hfix115_10_2 Q2.hinj115_10_2
      Q2.hcardT115_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_10_2 i) (Q2.hfix115_10_2 i) _)
      colCert_115_10_1.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T115_10
      hfix115_10 hinj115_10 hcardT115_10
      (fun i => conj_mem_of_fixedPoints _ _ (T115_10 i) (hfix115_10 i) _)
      ⟨115, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T115_10_2 Q2.hfix115_10_2 Q2.hinj115_10_2
      Q2.hcardT115_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_10_2 i) (Q2.hfix115_10_2 i) _)
      colCert_115_10_2.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T115_10
      hfix115_10 hinj115_10 hcardT115_10
      (fun i => conj_mem_of_fixedPoints _ _ (T115_10 i) (hfix115_10 i) _)
      ⟨115, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T115_10_2 Q2.hfix115_10_2 Q2.hinj115_10_2
      Q2.hcardT115_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_10_2 i) (Q2.hfix115_10_2 i) _)
      colCert_115_10_3.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T115_10
      hfix115_10 hinj115_10 hcardT115_10
      (fun i => conj_mem_of_fixedPoints _ _ (T115_10 i) (hfix115_10 i) _)
      ⟨115, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T115_10_2 Q2.hfix115_10_2 Q2.hinj115_10_2
      Q2.hcardT115_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_10_2 i) (Q2.hfix115_10_2 i) _)
      colCert_115_10_4.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T115_11
      hfix115_11 hinj115_11 hcardT115_11
      (fun i => conj_mem_of_fixedPoints _ _ (T115_11 i) (hfix115_11 i) _)
      ⟨115, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T115_11_2 Q2.hfix115_11_2 Q2.hinj115_11_2
      Q2.hcardT115_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_11_2 i) (Q2.hfix115_11_2 i) _)
      colCert_115_11_0.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T115_11
      hfix115_11 hinj115_11 hcardT115_11
      (fun i => conj_mem_of_fixedPoints _ _ (T115_11 i) (hfix115_11 i) _)
      ⟨115, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T115_11_2 Q2.hfix115_11_2 Q2.hinj115_11_2
      Q2.hcardT115_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_11_2 i) (Q2.hfix115_11_2 i) _)
      colCert_115_11_1.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T115_11
      hfix115_11 hinj115_11 hcardT115_11
      (fun i => conj_mem_of_fixedPoints _ _ (T115_11 i) (hfix115_11 i) _)
      ⟨115, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T115_11_2 Q2.hfix115_11_2 Q2.hinj115_11_2
      Q2.hcardT115_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_11_2 i) (Q2.hfix115_11_2 i) _)
      colCert_115_11_2.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T115_11
      hfix115_11 hinj115_11 hcardT115_11
      (fun i => conj_mem_of_fixedPoints _ _ (T115_11 i) (hfix115_11 i) _)
      ⟨115, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T115_11_2 Q2.hfix115_11_2 Q2.hinj115_11_2
      Q2.hcardT115_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_11_2 i) (Q2.hfix115_11_2 i) _)
      colCert_115_11_3.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T115_11
      hfix115_11 hinj115_11 hcardT115_11
      (fun i => conj_mem_of_fixedPoints _ _ (T115_11 i) (hfix115_11 i) _)
      ⟨115, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T115_11_2 Q2.hfix115_11_2 Q2.hinj115_11_2
      Q2.hcardT115_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_11_2 i) (Q2.hfix115_11_2 i) _)
      colCert_115_11_4.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T115_12
      hfix115_12 hinj115_12 hcardT115_12
      (fun i => conj_mem_of_fixedPoints _ _ (T115_12 i) (hfix115_12 i) _)
      ⟨115, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T115_12_2 Q2.hfix115_12_2 Q2.hinj115_12_2
      Q2.hcardT115_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_12_2 i) (Q2.hfix115_12_2 i) _)
      colCert_115_12_0.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T115_12
      hfix115_12 hinj115_12 hcardT115_12
      (fun i => conj_mem_of_fixedPoints _ _ (T115_12 i) (hfix115_12 i) _)
      ⟨115, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T115_12_2 Q2.hfix115_12_2 Q2.hinj115_12_2
      Q2.hcardT115_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_12_2 i) (Q2.hfix115_12_2 i) _)
      colCert_115_12_1.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T115_12
      hfix115_12 hinj115_12 hcardT115_12
      (fun i => conj_mem_of_fixedPoints _ _ (T115_12 i) (hfix115_12 i) _)
      ⟨115, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T115_12_2 Q2.hfix115_12_2 Q2.hinj115_12_2
      Q2.hcardT115_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_12_2 i) (Q2.hfix115_12_2 i) _)
      colCert_115_12_2.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T115_12
      hfix115_12 hinj115_12 hcardT115_12
      (fun i => conj_mem_of_fixedPoints _ _ (T115_12 i) (hfix115_12 i) _)
      ⟨115, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T115_12_2 Q2.hfix115_12_2 Q2.hinj115_12_2
      Q2.hcardT115_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_12_2 i) (Q2.hfix115_12_2 i) _)
      colCert_115_12_3.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T115_12
      hfix115_12 hinj115_12 hcardT115_12
      (fun i => conj_mem_of_fixedPoints _ _ (T115_12 i) (hfix115_12 i) _)
      ⟨115, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T115_12_2 Q2.hfix115_12_2 Q2.hinj115_12_2
      Q2.hcardT115_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_12_2 i) (Q2.hfix115_12_2 i) _)
      colCert_115_12_4.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T115_53
      hfix115_53 hinj115_53 hcardT115_53
      (fun i => conj_mem_of_fixedPoints _ _ (T115_53 i) (hfix115_53 i) _)
      ⟨115, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T115_53_2 Q2.hfix115_53_2 Q2.hinj115_53_2
      Q2.hcardT115_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_53_2 i) (Q2.hfix115_53_2 i) _)
      colCert_115_53_0.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T115_53
      hfix115_53 hinj115_53 hcardT115_53
      (fun i => conj_mem_of_fixedPoints _ _ (T115_53 i) (hfix115_53 i) _)
      ⟨115, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T115_53_2 Q2.hfix115_53_2 Q2.hinj115_53_2
      Q2.hcardT115_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_53_2 i) (Q2.hfix115_53_2 i) _)
      colCert_115_53_1.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T115_53
      hfix115_53 hinj115_53 hcardT115_53
      (fun i => conj_mem_of_fixedPoints _ _ (T115_53 i) (hfix115_53 i) _)
      ⟨115, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T115_53_2 Q2.hfix115_53_2 Q2.hinj115_53_2
      Q2.hcardT115_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_53_2 i) (Q2.hfix115_53_2 i) _)
      colCert_115_53_2.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T115_53
      hfix115_53 hinj115_53 hcardT115_53
      (fun i => conj_mem_of_fixedPoints _ _ (T115_53 i) (hfix115_53 i) _)
      ⟨115, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T115_53_2 Q2.hfix115_53_2 Q2.hinj115_53_2
      Q2.hcardT115_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_53_2 i) (Q2.hfix115_53_2 i) _)
      colCert_115_53_3.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T115_53
      hfix115_53 hinj115_53 hcardT115_53
      (fun i => conj_mem_of_fixedPoints _ _ (T115_53 i) (hfix115_53 i) _)
      ⟨115, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T115_53_2 Q2.hfix115_53_2 Q2.hinj115_53_2
      Q2.hcardT115_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_53_2 i) (Q2.hfix115_53_2 i) _)
      colCert_115_53_4.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T115_53
      hfix115_53 hinj115_53 hcardT115_53
      (fun i => conj_mem_of_fixedPoints _ _ (T115_53 i) (hfix115_53 i) _)
      ⟨115, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T115_53_2 Q2.hfix115_53_2 Q2.hinj115_53_2
      Q2.hcardT115_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_53_2 i) (Q2.hfix115_53_2 i) _)
      colCert_115_53_5.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T115_53
      hfix115_53 hinj115_53 hcardT115_53
      (fun i => conj_mem_of_fixedPoints _ _ (T115_53 i) (hfix115_53 i) _)
      ⟨115, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T115_53_2 Q2.hfix115_53_2 Q2.hinj115_53_2
      Q2.hcardT115_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_53_2 i) (Q2.hfix115_53_2 i) _)
      colCert_115_53_10.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T115_53
      hfix115_53 hinj115_53 hcardT115_53
      (fun i => conj_mem_of_fixedPoints _ _ (T115_53 i) (hfix115_53 i) _)
      ⟨115, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T115_53_2 Q2.hfix115_53_2 Q2.hinj115_53_2
      Q2.hcardT115_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_53_2 i) (Q2.hfix115_53_2 i) _)
      colCert_115_53_15.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T115_53
      hfix115_53 hinj115_53 hcardT115_53
      (fun i => conj_mem_of_fixedPoints _ _ (T115_53 i) (hfix115_53 i) _)
      ⟨115, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T115_53_2 Q2.hfix115_53_2 Q2.hinj115_53_2
      Q2.hcardT115_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_53_2 i) (Q2.hfix115_53_2 i) _)
      colCert_115_53_20.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T115_54
      hfix115_54 hinj115_54 hcardT115_54
      (fun i => conj_mem_of_fixedPoints _ _ (T115_54 i) (hfix115_54 i) _)
      ⟨115, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T115_54_2 Q2.hfix115_54_2 Q2.hinj115_54_2
      Q2.hcardT115_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_54_2 i) (Q2.hfix115_54_2 i) _)
      colCert_115_54_0.hD ?_).symm
  rw [alnId_115 j hj]


end LeanDring.P5Presentation
