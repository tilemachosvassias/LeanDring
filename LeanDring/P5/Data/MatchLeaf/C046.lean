/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C020
import LeanDring.P5.Data.ColCdd.C021
import LeanDring.P5.Data.ColRestCheap.C101
import LeanDring.P5.Data.ColRestCheap.C098
import LeanDring.P5.Data.ColRestCheap.C099
import LeanDring.P5.Data.ColRestCheap.C100
import LeanDring.P5.Data.EntryK.C041
import LeanDring.P5.Data.EntryK.C042
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C030
import LeanDring.P5.Data.SpeciesDiv.C031
import LeanDring.P5.Data.SpeciesDiv.C033
import LeanDring.P5.Data.SpeciesDiv.C034

/-! # Stage-5 leaves, chunk 45 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_142_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T142_54
      hfix142_54 hinj142_54 hcardT142_54
      (fun i => conj_mem_of_fixedPoints _ _ (T142_54 i) (hfix142_54 i) _)
      ⟨142, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T142_54_2 Q2.hfix142_54_2 Q2.hinj142_54_2
      Q2.hcardT142_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_54_2 i) (Q2.hfix142_54_2 i) _)
      colCert_142_54_10.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T142_54
      hfix142_54 hinj142_54 hcardT142_54
      (fun i => conj_mem_of_fixedPoints _ _ (T142_54 i) (hfix142_54 i) _)
      ⟨142, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T142_54_2 Q2.hfix142_54_2 Q2.hinj142_54_2
      Q2.hcardT142_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_54_2 i) (Q2.hfix142_54_2 i) _)
      colCert_142_54_15.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T142_54
      hfix142_54 hinj142_54 hcardT142_54
      (fun i => conj_mem_of_fixedPoints _ _ (T142_54 i) (hfix142_54 i) _)
      ⟨142, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T142_54_2 Q2.hfix142_54_2 Q2.hinj142_54_2
      Q2.hcardT142_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_54_2 i) (Q2.hfix142_54_2 i) _)
      colCert_142_54_20.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_90_0 (hp : 0 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 0 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      colCert_142_90_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_90_1 (hp : 1 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 1 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      colCert_142_90_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_90_2 (hp : 2 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 2 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      colCert_142_90_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_90_3 (hp : 3 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 3 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      colCert_142_90_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_90_4 (hp : 4 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 4 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      colCert_142_90_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_90_5 (hp : 5 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 5 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      colCert_142_90_5.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_90_10 (hp : 10 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 10 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      colCert_142_90_10.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_90_15 (hp : 15 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 15 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      colCert_142_90_15.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_90_20 (hp : 20 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 20 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      colCert_142_90_20.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_90_25 (hp : 25 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 25 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 25 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T142_90 = colFn colCertDiv_142_90_25.D1 (m := 5) from colCertDiv_142_90_25.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 25 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T142_90_2 = colFn colCertDiv_142_90_25.D2 (m := 5) from colCertDiv_142_90_25.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_90_25_match


theorem leaf_142_90_50 (hp : 50 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 50 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 50 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T142_90 = colFn colCertDiv_142_90_50.D1 (m := 5) from colCertDiv_142_90_50.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 50 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T142_90_2 = colFn colCertDiv_142_90_50.D2 (m := 5) from colCertDiv_142_90_50.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_90_50_match


theorem leaf_142_90_75 (hp : 75 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 75 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 75 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T142_90 = colFn colCertDiv_142_90_75.D1 (m := 5) from colCertDiv_142_90_75.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 75 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T142_90_2 = colFn colCertDiv_142_90_75.D2 (m := 5) from colCertDiv_142_90_75.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_90_75_match


theorem leaf_142_90_100 (hp : 100 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 100 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp)) T142_90
      hfix142_90 hinj142_90 hcardT142_90
      (fun i => conj_mem_of_fixedPoints _ _ (T142_90 i) (hfix142_90 i) _)
      ⟨142, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 100 hp) Q2.T142_90_2 Q2.hfix142_90_2 Q2.hinj142_90_2
      Q2.hcardT142_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_90_2 i) (Q2.hfix142_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T142_90 = colFn colCertDiv_142_90_100.D1 (m := 5) from colCertDiv_142_90_100.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 100 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T142_90_2 = colFn colCertDiv_142_90_100.D2 (m := 5) from colCertDiv_142_90_100.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_90_100_match


theorem leaf_142_91_0 (hp : 0 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp)) T142_91
      hfix142_91 hinj142_91 hcardT142_91
      (fun i => conj_mem_of_fixedPoints _ _ (T142_91 i) (hfix142_91 i) _)
      ⟨142, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 0 hp) Q2.T142_91_2 Q2.hfix142_91_2 Q2.hinj142_91_2
      Q2.hcardT142_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_91_2 i) (Q2.hfix142_91_2 i) _)
      colCert_142_91_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_91_1 (hp : 1 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp)) T142_91
      hfix142_91 hinj142_91 hcardT142_91
      (fun i => conj_mem_of_fixedPoints _ _ (T142_91 i) (hfix142_91 i) _)
      ⟨142, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 1 hp) Q2.T142_91_2 Q2.hfix142_91_2 Q2.hinj142_91_2
      Q2.hcardT142_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_91_2 i) (Q2.hfix142_91_2 i) _)
      colCert_142_91_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_91_2 (hp : 2 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp)) T142_91
      hfix142_91 hinj142_91 hcardT142_91
      (fun i => conj_mem_of_fixedPoints _ _ (T142_91 i) (hfix142_91 i) _)
      ⟨142, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 2 hp) Q2.T142_91_2 Q2.hfix142_91_2 Q2.hinj142_91_2
      Q2.hcardT142_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_91_2 i) (Q2.hfix142_91_2 i) _)
      colCert_142_91_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_91_3 (hp : 3 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp)) T142_91
      hfix142_91 hinj142_91 hcardT142_91
      (fun i => conj_mem_of_fixedPoints _ _ (T142_91 i) (hfix142_91 i) _)
      ⟨142, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 3 hp) Q2.T142_91_2 Q2.hfix142_91_2 Q2.hinj142_91_2
      Q2.hcardT142_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_91_2 i) (Q2.hfix142_91_2 i) _)
      colCert_142_91_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_91_4 (hp : 4 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp)) T142_91
      hfix142_91 hinj142_91 hcardT142_91
      (fun i => conj_mem_of_fixedPoints _ _ (T142_91 i) (hfix142_91 i) _)
      ⟨142, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 4 hp) Q2.T142_91_2 Q2.hfix142_91_2 Q2.hinj142_91_2
      Q2.hcardT142_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_91_2 i) (Q2.hfix142_91_2 i) _)
      colCert_142_91_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_91_5 (hp : 5 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp)) T142_91
      hfix142_91 hinj142_91 hcardT142_91
      (fun i => conj_mem_of_fixedPoints _ _ (T142_91 i) (hfix142_91 i) _)
      ⟨142, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 5 hp) Q2.T142_91_2 Q2.hfix142_91_2 Q2.hinj142_91_2
      Q2.hcardT142_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_91_2 i) (Q2.hfix142_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T142_91 = colFn colCertDiv_142_91_5.D1 (m := 5) from colCertDiv_142_91_5.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 5 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T142_91_2 = colFn colCertDiv_142_91_5.D2 (m := 5) from colCertDiv_142_91_5.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_91_5_match


theorem leaf_142_91_10 (hp : 10 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp)) T142_91
      hfix142_91 hinj142_91 hcardT142_91
      (fun i => conj_mem_of_fixedPoints _ _ (T142_91 i) (hfix142_91 i) _)
      ⟨142, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 10 hp) Q2.T142_91_2 Q2.hfix142_91_2 Q2.hinj142_91_2
      Q2.hcardT142_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_91_2 i) (Q2.hfix142_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T142_91 = colFn colCertDiv_142_91_10.D1 (m := 5) from colCertDiv_142_91_10.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 10 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T142_91_2 = colFn colCertDiv_142_91_10.D2 (m := 5) from colCertDiv_142_91_10.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_91_10_match


theorem leaf_142_91_15 (hp : 15 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp)) T142_91
      hfix142_91 hinj142_91 hcardT142_91
      (fun i => conj_mem_of_fixedPoints _ _ (T142_91 i) (hfix142_91 i) _)
      ⟨142, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 15 hp) Q2.T142_91_2 Q2.hfix142_91_2 Q2.hinj142_91_2
      Q2.hcardT142_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_91_2 i) (Q2.hfix142_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T142_91 = colFn colCertDiv_142_91_15.D1 (m := 5) from colCertDiv_142_91_15.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 15 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T142_91_2 = colFn colCertDiv_142_91_15.D2 (m := 5) from colCertDiv_142_91_15.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_91_15_match


theorem leaf_142_91_20 (hp : 20 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp)) T142_91
      hfix142_91 hinj142_91 hcardT142_91
      (fun i => conj_mem_of_fixedPoints _ _ (T142_91 i) (hfix142_91 i) _)
      ⟨142, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 20 hp) Q2.T142_91_2 Q2.hfix142_91_2 Q2.hinj142_91_2
      Q2.hcardT142_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_91_2 i) (Q2.hfix142_91_2 i) _)
      colCert_142_91_20.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_92_0 (hp : 0 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp)) T142_92
      hfix142_92 hinj142_92 hcardT142_92
      (fun i => conj_mem_of_fixedPoints _ _ (T142_92 i) (hfix142_92 i) _)
      ⟨142, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 0 hp) Q2.T142_92_2 Q2.hfix142_92_2 Q2.hinj142_92_2
      Q2.hcardT142_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_92_2 i) (Q2.hfix142_92_2 i) _)
      colCert_142_92_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_92_1 (hp : 1 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp)) T142_92
      hfix142_92 hinj142_92 hcardT142_92
      (fun i => conj_mem_of_fixedPoints _ _ (T142_92 i) (hfix142_92 i) _)
      ⟨142, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 1 hp) Q2.T142_92_2 Q2.hfix142_92_2 Q2.hinj142_92_2
      Q2.hcardT142_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_92_2 i) (Q2.hfix142_92_2 i) _)
      colCert_142_92_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_92_2 (hp : 2 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp)) T142_92
      hfix142_92 hinj142_92 hcardT142_92
      (fun i => conj_mem_of_fixedPoints _ _ (T142_92 i) (hfix142_92 i) _)
      ⟨142, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 2 hp) Q2.T142_92_2 Q2.hfix142_92_2 Q2.hinj142_92_2
      Q2.hcardT142_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_92_2 i) (Q2.hfix142_92_2 i) _)
      colCert_142_92_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_92_3 (hp : 3 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp)) T142_92
      hfix142_92 hinj142_92 hcardT142_92
      (fun i => conj_mem_of_fixedPoints _ _ (T142_92 i) (hfix142_92 i) _)
      ⟨142, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 3 hp) Q2.T142_92_2 Q2.hfix142_92_2 Q2.hinj142_92_2
      Q2.hcardT142_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_92_2 i) (Q2.hfix142_92_2 i) _)
      colCert_142_92_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_92_4 (hp : 4 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp)) T142_92
      hfix142_92 hinj142_92 hcardT142_92
      (fun i => conj_mem_of_fixedPoints _ _ (T142_92 i) (hfix142_92 i) _)
      ⟨142, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 4 hp) Q2.T142_92_2 Q2.hfix142_92_2 Q2.hinj142_92_2
      Q2.hcardT142_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_92_2 i) (Q2.hfix142_92_2 i) _)
      colCert_142_92_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_92_5 (hp : 5 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp)) T142_92
      hfix142_92 hinj142_92 hcardT142_92
      (fun i => conj_mem_of_fixedPoints _ _ (T142_92 i) (hfix142_92 i) _)
      ⟨142, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 5 hp) Q2.T142_92_2 Q2.hfix142_92_2 Q2.hinj142_92_2
      Q2.hcardT142_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_92_2 i) (Q2.hfix142_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T142_92 = colFn colCertDiv_142_92_5.D1 (m := 5) from colCertDiv_142_92_5.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 5 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T142_92_2 = colFn colCertDiv_142_92_5.D2 (m := 5) from colCertDiv_142_92_5.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_92_5_match


theorem leaf_142_92_10 (hp : 10 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp)) T142_92
      hfix142_92 hinj142_92 hcardT142_92
      (fun i => conj_mem_of_fixedPoints _ _ (T142_92 i) (hfix142_92 i) _)
      ⟨142, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 10 hp) Q2.T142_92_2 Q2.hfix142_92_2 Q2.hinj142_92_2
      Q2.hcardT142_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_92_2 i) (Q2.hfix142_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T142_92 = colFn colCertDiv_142_92_10.D1 (m := 5) from colCertDiv_142_92_10.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 10 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T142_92_2 = colFn colCertDiv_142_92_10.D2 (m := 5) from colCertDiv_142_92_10.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_92_10_match


theorem leaf_142_92_15 (hp : 15 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp)) T142_92
      hfix142_92 hinj142_92 hcardT142_92
      (fun i => conj_mem_of_fixedPoints _ _ (T142_92 i) (hfix142_92 i) _)
      ⟨142, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 15 hp) Q2.T142_92_2 Q2.hfix142_92_2 Q2.hinj142_92_2
      Q2.hcardT142_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_92_2 i) (Q2.hfix142_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T142_92 = colFn colCertDiv_142_92_15.D1 (m := 5) from colCertDiv_142_92_15.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 15 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T142_92_2 = colFn colCertDiv_142_92_15.D2 (m := 5) from colCertDiv_142_92_15.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_92_15_match


theorem leaf_142_92_20 (hp : 20 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp)) T142_92
      hfix142_92 hinj142_92 hcardT142_92
      (fun i => conj_mem_of_fixedPoints _ _ (T142_92 i) (hfix142_92 i) _)
      ⟨142, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 20 hp) Q2.T142_92_2 Q2.hfix142_92_2 Q2.hinj142_92_2
      Q2.hcardT142_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_92_2 i) (Q2.hfix142_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T142_92 = colFn colCertDiv_142_92_20.D1 (m := 5) from colCertDiv_142_92_20.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 20 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T142_92_2 = colFn colCertDiv_142_92_20.D2 (m := 5) from colCertDiv_142_92_20.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_92_20_match


theorem leaf_142_93_0 (hp : 0 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp)) T142_93
      hfix142_93 hinj142_93 hcardT142_93
      (fun i => conj_mem_of_fixedPoints _ _ (T142_93 i) (hfix142_93 i) _)
      ⟨142, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 0 hp) Q2.T142_93_2 Q2.hfix142_93_2 Q2.hinj142_93_2
      Q2.hcardT142_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_93_2 i) (Q2.hfix142_93_2 i) _)
      colCert_142_93_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_93_1 (hp : 1 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp)) T142_93
      hfix142_93 hinj142_93 hcardT142_93
      (fun i => conj_mem_of_fixedPoints _ _ (T142_93 i) (hfix142_93 i) _)
      ⟨142, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 1 hp) Q2.T142_93_2 Q2.hfix142_93_2 Q2.hinj142_93_2
      Q2.hcardT142_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_93_2 i) (Q2.hfix142_93_2 i) _)
      colCert_142_93_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_93_2 (hp : 2 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp)) T142_93
      hfix142_93 hinj142_93 hcardT142_93
      (fun i => conj_mem_of_fixedPoints _ _ (T142_93 i) (hfix142_93 i) _)
      ⟨142, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 2 hp) Q2.T142_93_2 Q2.hfix142_93_2 Q2.hinj142_93_2
      Q2.hcardT142_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_93_2 i) (Q2.hfix142_93_2 i) _)
      colCert_142_93_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_93_3 (hp : 3 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp)) T142_93
      hfix142_93 hinj142_93 hcardT142_93
      (fun i => conj_mem_of_fixedPoints _ _ (T142_93 i) (hfix142_93 i) _)
      ⟨142, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 3 hp) Q2.T142_93_2 Q2.hfix142_93_2 Q2.hinj142_93_2
      Q2.hcardT142_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_93_2 i) (Q2.hfix142_93_2 i) _)
      colCert_142_93_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_93_4 (hp : 4 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp)) T142_93
      hfix142_93 hinj142_93 hcardT142_93
      (fun i => conj_mem_of_fixedPoints _ _ (T142_93 i) (hfix142_93 i) _)
      ⟨142, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 4 hp) Q2.T142_93_2 Q2.hfix142_93_2 Q2.hinj142_93_2
      Q2.hcardT142_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_93_2 i) (Q2.hfix142_93_2 i) _)
      colCert_142_93_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_93_5 (hp : 5 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp)) T142_93
      hfix142_93 hinj142_93 hcardT142_93
      (fun i => conj_mem_of_fixedPoints _ _ (T142_93 i) (hfix142_93 i) _)
      ⟨142, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 5 hp) Q2.T142_93_2 Q2.hfix142_93_2 Q2.hinj142_93_2
      Q2.hcardT142_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_93_2 i) (Q2.hfix142_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T142_93 = colFn colCertDiv_142_93_5.D1 (m := 5) from colCertDiv_142_93_5.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 5 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T142_93_2 = colFn colCertDiv_142_93_5.D2 (m := 5) from colCertDiv_142_93_5.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_93_5_match


theorem leaf_142_93_10 (hp : 10 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp)) T142_93
      hfix142_93 hinj142_93 hcardT142_93
      (fun i => conj_mem_of_fixedPoints _ _ (T142_93 i) (hfix142_93 i) _)
      ⟨142, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 10 hp) Q2.T142_93_2 Q2.hfix142_93_2 Q2.hinj142_93_2
      Q2.hcardT142_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_93_2 i) (Q2.hfix142_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T142_93 = colFn colCertDiv_142_93_10.D1 (m := 5) from colCertDiv_142_93_10.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 10 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T142_93_2 = colFn colCertDiv_142_93_10.D2 (m := 5) from colCertDiv_142_93_10.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_93_10_match


theorem leaf_142_93_15 (hp : 15 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp)) T142_93
      hfix142_93 hinj142_93 hcardT142_93
      (fun i => conj_mem_of_fixedPoints _ _ (T142_93 i) (hfix142_93 i) _)
      ⟨142, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 15 hp) Q2.T142_93_2 Q2.hfix142_93_2 Q2.hinj142_93_2
      Q2.hcardT142_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_93_2 i) (Q2.hfix142_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T142_93 = colFn colCertDiv_142_93_15.D1 (m := 5) from colCertDiv_142_93_15.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 15 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T142_93_2 = colFn colCertDiv_142_93_15.D2 (m := 5) from colCertDiv_142_93_15.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_93_15_match


theorem leaf_142_93_20 (hp : 20 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp)) T142_93
      hfix142_93 hinj142_93 hcardT142_93
      (fun i => conj_mem_of_fixedPoints _ _ (T142_93 i) (hfix142_93 i) _)
      ⟨142, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 20 hp) Q2.T142_93_2 Q2.hfix142_93_2 Q2.hinj142_93_2
      Q2.hcardT142_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_93_2 i) (Q2.hfix142_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T142_93 = colFn colCertDiv_142_93_20.D1 (m := 5) from colCertDiv_142_93_20.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 20 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T142_93_2 = colFn colCertDiv_142_93_20.D2 (m := 5) from colCertDiv_142_93_20.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_93_20_match


theorem leaf_142_94_0 (hp : 0 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp)) T142_94
      hfix142_94 hinj142_94 hcardT142_94
      (fun i => conj_mem_of_fixedPoints _ _ (T142_94 i) (hfix142_94 i) _)
      ⟨142, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 0 hp) Q2.T142_94_2 Q2.hfix142_94_2 Q2.hinj142_94_2
      Q2.hcardT142_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_94_2 i) (Q2.hfix142_94_2 i) _)
      colCert_142_94_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_94_1 (hp : 1 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp)) T142_94
      hfix142_94 hinj142_94 hcardT142_94
      (fun i => conj_mem_of_fixedPoints _ _ (T142_94 i) (hfix142_94 i) _)
      ⟨142, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 1 hp) Q2.T142_94_2 Q2.hfix142_94_2 Q2.hinj142_94_2
      Q2.hcardT142_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_94_2 i) (Q2.hfix142_94_2 i) _)
      colCert_142_94_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_94_2 (hp : 2 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp)) T142_94
      hfix142_94 hinj142_94 hcardT142_94
      (fun i => conj_mem_of_fixedPoints _ _ (T142_94 i) (hfix142_94 i) _)
      ⟨142, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 2 hp) Q2.T142_94_2 Q2.hfix142_94_2 Q2.hinj142_94_2
      Q2.hcardT142_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_94_2 i) (Q2.hfix142_94_2 i) _)
      colCert_142_94_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_94_3 (hp : 3 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp)) T142_94
      hfix142_94 hinj142_94 hcardT142_94
      (fun i => conj_mem_of_fixedPoints _ _ (T142_94 i) (hfix142_94 i) _)
      ⟨142, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 3 hp) Q2.T142_94_2 Q2.hfix142_94_2 Q2.hinj142_94_2
      Q2.hcardT142_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_94_2 i) (Q2.hfix142_94_2 i) _)
      colCert_142_94_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_94_4 (hp : 4 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp)) T142_94
      hfix142_94 hinj142_94 hcardT142_94
      (fun i => conj_mem_of_fixedPoints _ _ (T142_94 i) (hfix142_94 i) _)
      ⟨142, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 4 hp) Q2.T142_94_2 Q2.hfix142_94_2 Q2.hinj142_94_2
      Q2.hcardT142_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_94_2 i) (Q2.hfix142_94_2 i) _)
      colCert_142_94_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_94_5 (hp : 5 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp)) T142_94
      hfix142_94 hinj142_94 hcardT142_94
      (fun i => conj_mem_of_fixedPoints _ _ (T142_94 i) (hfix142_94 i) _)
      ⟨142, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 5 hp) Q2.T142_94_2 Q2.hfix142_94_2 Q2.hinj142_94_2
      Q2.hcardT142_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_94_2 i) (Q2.hfix142_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T142_94 = colFn colCertDiv_142_94_5.D1 (m := 5) from colCertDiv_142_94_5.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 5 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T142_94_2 = colFn colCertDiv_142_94_5.D2 (m := 5) from colCertDiv_142_94_5.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_94_5_match


theorem leaf_142_94_10 (hp : 10 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp)) T142_94
      hfix142_94 hinj142_94 hcardT142_94
      (fun i => conj_mem_of_fixedPoints _ _ (T142_94 i) (hfix142_94 i) _)
      ⟨142, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 10 hp) Q2.T142_94_2 Q2.hfix142_94_2 Q2.hinj142_94_2
      Q2.hcardT142_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_94_2 i) (Q2.hfix142_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T142_94 = colFn colCertDiv_142_94_10.D1 (m := 5) from colCertDiv_142_94_10.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 10 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T142_94_2 = colFn colCertDiv_142_94_10.D2 (m := 5) from colCertDiv_142_94_10.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_94_10_match


theorem leaf_142_94_15 (hp : 15 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp)) T142_94
      hfix142_94 hinj142_94 hcardT142_94
      (fun i => conj_mem_of_fixedPoints _ _ (T142_94 i) (hfix142_94 i) _)
      ⟨142, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 15 hp) Q2.T142_94_2 Q2.hfix142_94_2 Q2.hinj142_94_2
      Q2.hcardT142_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_94_2 i) (Q2.hfix142_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T142_94 = colFn colCertDiv_142_94_15.D1 (m := 5) from colCertDiv_142_94_15.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 15 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T142_94_2 = colFn colCertDiv_142_94_15.D2 (m := 5) from colCertDiv_142_94_15.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_94_15_match


theorem leaf_142_94_20 (hp : 20 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨142, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp)) T142_94
      hfix142_94 hinj142_94 hcardT142_94
      (fun i => conj_mem_of_fixedPoints _ _ (T142_94 i) (hfix142_94 i) _)
      ⟨142, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 20 hp) Q2.T142_94_2 Q2.hfix142_94_2 Q2.hinj142_94_2
      Q2.hcardT142_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_94_2 i) (Q2.hfix142_94_2 i) _)
      ?_).symm
  rw [show colData1 (⟨142, by decide⟩ : Fin 148)
        ((colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp) : ↥(reps ⟨94, by decide⟩)) : Coordinate 1)
        T142_94 = colFn colCertDiv_142_94_20.D1 (m := 5) from colCertDiv_142_94_20.bind1,
    show colData2 (⟨142, by decide⟩ : Fin 148)
        ((colE2 ⟨94, by decide⟩ 20 hp : ↥(Q2.reps ⟨94, by decide⟩)) : Coordinate 2)
        Q2.T142_94_2 = colFn colCertDiv_142_94_20.D2 (m := 5) from colCertDiv_142_94_20.bind2]
  rw [alnId_142 j hj]
  exact fastcode_of_div ⟨142, by decide⟩ _ _ _
    ((alnId_142 j hj) ▸ Q2.listedAt (⟨142, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨142, by decide⟩ : Fin 148) hj hq).1) colCertDiv_142_94_20_match


theorem leaf_142_115_0 (hp : 0 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp)) T142_115
      hfix142_115 hinj142_115 hcardT142_115
      (fun i => conj_mem_of_fixedPoints _ _ (T142_115 i) (hfix142_115 i) _)
      ⟨142, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 0 hp) Q2.T142_115_2 Q2.hfix142_115_2 Q2.hinj142_115_2
      Q2.hcardT142_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_115_2 i) (Q2.hfix142_115_2 i) _)
      colCert_142_115_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_115_1 (hp : 1 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp)) T142_115
      hfix142_115 hinj142_115 hcardT142_115
      (fun i => conj_mem_of_fixedPoints _ _ (T142_115 i) (hfix142_115 i) _)
      ⟨142, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 1 hp) Q2.T142_115_2 Q2.hfix142_115_2 Q2.hinj142_115_2
      Q2.hcardT142_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_115_2 i) (Q2.hfix142_115_2 i) _)
      colCert_142_115_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_115_2 (hp : 2 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp)) T142_115
      hfix142_115 hinj142_115 hcardT142_115
      (fun i => conj_mem_of_fixedPoints _ _ (T142_115 i) (hfix142_115 i) _)
      ⟨142, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 2 hp) Q2.T142_115_2 Q2.hfix142_115_2 Q2.hinj142_115_2
      Q2.hcardT142_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_115_2 i) (Q2.hfix142_115_2 i) _)
      colCert_142_115_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_115_3 (hp : 3 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp)) T142_115
      hfix142_115 hinj142_115 hcardT142_115
      (fun i => conj_mem_of_fixedPoints _ _ (T142_115 i) (hfix142_115 i) _)
      ⟨142, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 3 hp) Q2.T142_115_2 Q2.hfix142_115_2 Q2.hinj142_115_2
      Q2.hcardT142_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_115_2 i) (Q2.hfix142_115_2 i) _)
      colCert_142_115_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_115_4 (hp : 4 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp)) T142_115
      hfix142_115 hinj142_115 hcardT142_115
      (fun i => conj_mem_of_fixedPoints _ _ (T142_115 i) (hfix142_115 i) _)
      ⟨142, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 4 hp) Q2.T142_115_2 Q2.hfix142_115_2 Q2.hinj142_115_2
      Q2.hcardT142_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_115_2 i) (Q2.hfix142_115_2 i) _)
      colCert_142_115_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_115_5 (hp : 5 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp)) T142_115
      hfix142_115 hinj142_115 hcardT142_115
      (fun i => conj_mem_of_fixedPoints _ _ (T142_115 i) (hfix142_115 i) _)
      ⟨142, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 5 hp) Q2.T142_115_2 Q2.hfix142_115_2 Q2.hinj142_115_2
      Q2.hcardT142_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_115_2 i) (Q2.hfix142_115_2 i) _)
      colCert_142_115_5.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_115_10 (hp : 10 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp)) T142_115
      hfix142_115 hinj142_115 hcardT142_115
      (fun i => conj_mem_of_fixedPoints _ _ (T142_115 i) (hfix142_115 i) _)
      ⟨142, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 10 hp) Q2.T142_115_2 Q2.hfix142_115_2 Q2.hinj142_115_2
      Q2.hcardT142_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_115_2 i) (Q2.hfix142_115_2 i) _)
      colCert_142_115_10.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_115_15 (hp : 15 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp)) T142_115
      hfix142_115 hinj142_115 hcardT142_115
      (fun i => conj_mem_of_fixedPoints _ _ (T142_115 i) (hfix142_115 i) _)
      ⟨142, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 15 hp) Q2.T142_115_2 Q2.hfix142_115_2 Q2.hinj142_115_2
      Q2.hcardT142_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_115_2 i) (Q2.hfix142_115_2 i) _)
      colCert_142_115_15.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_115_20 (hp : 20 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp)) T142_115
      hfix142_115 hinj142_115 hcardT142_115
      (fun i => conj_mem_of_fixedPoints _ _ (T142_115 i) (hfix142_115 i) _)
      ⟨142, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 20 hp) Q2.T142_115_2 Q2.hfix142_115_2 Q2.hinj142_115_2
      Q2.hcardT142_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_115_2 i) (Q2.hfix142_115_2 i) _)
      colCert_142_115_20.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_0 (hp : 0 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 0 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 0 (transLenTr ⟨142, by decide⟩ 0 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 0 (transLenTr ⟨142, by decide⟩ 0 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 0 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_0.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_1 (hp : 1 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 1 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 1 (transLenTr ⟨142, by decide⟩ 1 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 1 (transLenTr ⟨142, by decide⟩ 1 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 1 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_1.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_2 (hp : 2 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 2 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 2 (transLenTr ⟨142, by decide⟩ 2 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 2 (transLenTr ⟨142, by decide⟩ 2 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 2 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_2.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_3 (hp : 3 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 3 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 3 (transLenTr ⟨142, by decide⟩ 3 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 3 (transLenTr ⟨142, by decide⟩ 3 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 3 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_3.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_4 (hp : 4 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 4 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 4 (transLenTr ⟨142, by decide⟩ 4 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 4 (transLenTr ⟨142, by decide⟩ 4 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 4 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_4.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_5 (hp : 5 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 5 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 5 (transLenTr ⟨142, by decide⟩ 5 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 5 (transLenTr ⟨142, by decide⟩ 5 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 5 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_5.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_6 (hp : 6 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 6 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 6 (transLenTr ⟨142, by decide⟩ 6 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 6 (transLenTr ⟨142, by decide⟩ 6 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 6 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_6.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_7 (hp : 7 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 7 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 7 (transLenTr ⟨142, by decide⟩ 7 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 7 (transLenTr ⟨142, by decide⟩ 7 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 7 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_7.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_8 (hp : 8 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 8 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 8 (transLenTr ⟨142, by decide⟩ 8 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 8 (transLenTr ⟨142, by decide⟩ 8 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 8 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_8.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_9 (hp : 9 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 9 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 9 (transLenTr ⟨142, by decide⟩ 9 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 9 (transLenTr ⟨142, by decide⟩ 9 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 9 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_9.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_10 (hp : 10 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 10 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 10 (transLenTr ⟨142, by decide⟩ 10 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 10 (transLenTr ⟨142, by decide⟩ 10 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 10 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_10.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_11 (hp : 11 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 11 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 11 (transLenTr ⟨142, by decide⟩ 11 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 11 (transLenTr ⟨142, by decide⟩ 11 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 11 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_11.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_12 (hp : 12 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 12 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 12 (transLenTr ⟨142, by decide⟩ 12 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 12 (transLenTr ⟨142, by decide⟩ 12 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 12 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_12.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_13 (hp : 13 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 13 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 13 (transLenTr ⟨142, by decide⟩ 13 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 13 (transLenTr ⟨142, by decide⟩ 13 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 13 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_13.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_14 (hp : 14 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 14 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 14 (transLenTr ⟨142, by decide⟩ 14 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 14 (transLenTr ⟨142, by decide⟩ 14 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 14 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_14.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_15 (hp : 15 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 15 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 15 (transLenTr ⟨142, by decide⟩ 15 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 15 (transLenTr ⟨142, by decide⟩ 15 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 15 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_15.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_16 (hp : 16 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 16 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 16 (transLenTr ⟨142, by decide⟩ 16 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 16 (transLenTr ⟨142, by decide⟩ 16 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 16 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_16.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_17 (hp : 17 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 17 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 17 (transLenTr ⟨142, by decide⟩ 17 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 17 (transLenTr ⟨142, by decide⟩ 17 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 17 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_17.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_18 (hp : 18 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 18 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 18 (transLenTr ⟨142, by decide⟩ 18 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 18 (transLenTr ⟨142, by decide⟩ 18 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 18 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_18.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_19 (hp : 19 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 19 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 19 (transLenTr ⟨142, by decide⟩ 19 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 19 (transLenTr ⟨142, by decide⟩ 19 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 19 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_19.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_20 (hp : 20 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 20 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 20 (transLenTr ⟨142, by decide⟩ 20 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 20 (transLenTr ⟨142, by decide⟩ 20 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 20 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_20.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_21 (hp : 21 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 21 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 21 (transLenTr ⟨142, by decide⟩ 21 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 21 (transLenTr ⟨142, by decide⟩ 21 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 21 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_21.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_22 (hp : 22 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 22 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 22 (transLenTr ⟨142, by decide⟩ 22 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 22 (transLenTr ⟨142, by decide⟩ 22 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 22 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_22.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_23 (hp : 23 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 23 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 23 (transLenTr ⟨142, by decide⟩ 23 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 23 (transLenTr ⟨142, by decide⟩ 23 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 23 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_23.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_142_142_24 (hp : 24 < (Q2.transData.getD 142 []).length)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ 24 hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ 24 (transLenTr ⟨142, by decide⟩ 24 hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨142, by decide⟩ : Fin 148) ⟨142, by decide⟩ _
      (validAt ⟨142, by decide⟩ (listedAt ⟨142, by decide⟩ hj))
      (colE1 ⟨142, by decide⟩ 24 (transLenTr ⟨142, by decide⟩ 24 hp)) T142_142
      hfix142_142 hinj142_142 hcardT142_142
      (fun i => conj_mem_of_fixedPoints _ _ (T142_142 i) (hfix142_142 i) _)
      ⟨142, by decide⟩ ⟨142, by decide⟩ _
      (Q2.validAt ⟨142, by decide⟩ (Q2.listedAt ⟨142, by decide⟩
        (alnCheck_rep ⟨142, by decide⟩ hj hq).1))
      (colE2 ⟨142, by decide⟩ 24 hp) Q2.T142_142_2 Q2.hfix142_142_2 Q2.hinj142_142_2
      Q2.hcardT142_142_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T142_142_2 i) (Q2.hfix142_142_2 i) _)
      colCert_142_142_24.hD ?_).symm
  rw [alnId_142 j hj]


theorem leaf_143_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T143_10
      hfix143_10 hinj143_10 hcardT143_10
      (fun i => conj_mem_of_fixedPoints _ _ (T143_10 i) (hfix143_10 i) _)
      ⟨143, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T143_10_2 Q2.hfix143_10_2 Q2.hinj143_10_2
      Q2.hcardT143_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_10_2 i) (Q2.hfix143_10_2 i) _)
      colCert_143_10_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T143_10
      hfix143_10 hinj143_10 hcardT143_10
      (fun i => conj_mem_of_fixedPoints _ _ (T143_10 i) (hfix143_10 i) _)
      ⟨143, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T143_10_2 Q2.hfix143_10_2 Q2.hinj143_10_2
      Q2.hcardT143_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_10_2 i) (Q2.hfix143_10_2 i) _)
      colCert_143_10_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T143_10
      hfix143_10 hinj143_10 hcardT143_10
      (fun i => conj_mem_of_fixedPoints _ _ (T143_10 i) (hfix143_10 i) _)
      ⟨143, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T143_10_2 Q2.hfix143_10_2 Q2.hinj143_10_2
      Q2.hcardT143_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_10_2 i) (Q2.hfix143_10_2 i) _)
      colCert_143_10_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T143_10
      hfix143_10 hinj143_10 hcardT143_10
      (fun i => conj_mem_of_fixedPoints _ _ (T143_10 i) (hfix143_10 i) _)
      ⟨143, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T143_10_2 Q2.hfix143_10_2 Q2.hinj143_10_2
      Q2.hcardT143_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_10_2 i) (Q2.hfix143_10_2 i) _)
      colCert_143_10_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T143_10
      hfix143_10 hinj143_10 hcardT143_10
      (fun i => conj_mem_of_fixedPoints _ _ (T143_10 i) (hfix143_10 i) _)
      ⟨143, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T143_10_2 Q2.hfix143_10_2 Q2.hinj143_10_2
      Q2.hcardT143_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_10_2 i) (Q2.hfix143_10_2 i) _)
      colCert_143_10_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T143_11
      hfix143_11 hinj143_11 hcardT143_11
      (fun i => conj_mem_of_fixedPoints _ _ (T143_11 i) (hfix143_11 i) _)
      ⟨143, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T143_11_2 Q2.hfix143_11_2 Q2.hinj143_11_2
      Q2.hcardT143_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_11_2 i) (Q2.hfix143_11_2 i) _)
      colCert_143_11_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T143_11
      hfix143_11 hinj143_11 hcardT143_11
      (fun i => conj_mem_of_fixedPoints _ _ (T143_11 i) (hfix143_11 i) _)
      ⟨143, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T143_11_2 Q2.hfix143_11_2 Q2.hinj143_11_2
      Q2.hcardT143_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_11_2 i) (Q2.hfix143_11_2 i) _)
      colCert_143_11_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T143_11
      hfix143_11 hinj143_11 hcardT143_11
      (fun i => conj_mem_of_fixedPoints _ _ (T143_11 i) (hfix143_11 i) _)
      ⟨143, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T143_11_2 Q2.hfix143_11_2 Q2.hinj143_11_2
      Q2.hcardT143_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_11_2 i) (Q2.hfix143_11_2 i) _)
      colCert_143_11_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T143_11
      hfix143_11 hinj143_11 hcardT143_11
      (fun i => conj_mem_of_fixedPoints _ _ (T143_11 i) (hfix143_11 i) _)
      ⟨143, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T143_11_2 Q2.hfix143_11_2 Q2.hinj143_11_2
      Q2.hcardT143_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_11_2 i) (Q2.hfix143_11_2 i) _)
      colCert_143_11_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T143_11
      hfix143_11 hinj143_11 hcardT143_11
      (fun i => conj_mem_of_fixedPoints _ _ (T143_11 i) (hfix143_11 i) _)
      ⟨143, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T143_11_2 Q2.hfix143_11_2 Q2.hinj143_11_2
      Q2.hcardT143_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_11_2 i) (Q2.hfix143_11_2 i) _)
      colCert_143_11_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T143_12
      hfix143_12 hinj143_12 hcardT143_12
      (fun i => conj_mem_of_fixedPoints _ _ (T143_12 i) (hfix143_12 i) _)
      ⟨143, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T143_12_2 Q2.hfix143_12_2 Q2.hinj143_12_2
      Q2.hcardT143_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_12_2 i) (Q2.hfix143_12_2 i) _)
      colCert_143_12_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T143_12
      hfix143_12 hinj143_12 hcardT143_12
      (fun i => conj_mem_of_fixedPoints _ _ (T143_12 i) (hfix143_12 i) _)
      ⟨143, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T143_12_2 Q2.hfix143_12_2 Q2.hinj143_12_2
      Q2.hcardT143_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_12_2 i) (Q2.hfix143_12_2 i) _)
      colCert_143_12_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T143_12
      hfix143_12 hinj143_12 hcardT143_12
      (fun i => conj_mem_of_fixedPoints _ _ (T143_12 i) (hfix143_12 i) _)
      ⟨143, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T143_12_2 Q2.hfix143_12_2 Q2.hinj143_12_2
      Q2.hcardT143_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_12_2 i) (Q2.hfix143_12_2 i) _)
      colCert_143_12_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T143_12
      hfix143_12 hinj143_12 hcardT143_12
      (fun i => conj_mem_of_fixedPoints _ _ (T143_12 i) (hfix143_12 i) _)
      ⟨143, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T143_12_2 Q2.hfix143_12_2 Q2.hinj143_12_2
      Q2.hcardT143_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_12_2 i) (Q2.hfix143_12_2 i) _)
      colCert_143_12_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T143_12
      hfix143_12 hinj143_12 hcardT143_12
      (fun i => conj_mem_of_fixedPoints _ _ (T143_12 i) (hfix143_12 i) _)
      ⟨143, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T143_12_2 Q2.hfix143_12_2 Q2.hinj143_12_2
      Q2.hcardT143_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_12_2 i) (Q2.hfix143_12_2 i) _)
      colCert_143_12_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T143_33
      hfix143_33 hinj143_33 hcardT143_33
      (fun i => conj_mem_of_fixedPoints _ _ (T143_33 i) (hfix143_33 i) _)
      ⟨143, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T143_33_2 Q2.hfix143_33_2 Q2.hinj143_33_2
      Q2.hcardT143_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_33_2 i) (Q2.hfix143_33_2 i) _)
      colCert_143_33_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T143_33
      hfix143_33 hinj143_33 hcardT143_33
      (fun i => conj_mem_of_fixedPoints _ _ (T143_33 i) (hfix143_33 i) _)
      ⟨143, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T143_33_2 Q2.hfix143_33_2 Q2.hinj143_33_2
      Q2.hcardT143_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_33_2 i) (Q2.hfix143_33_2 i) _)
      colCert_143_33_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T143_33
      hfix143_33 hinj143_33 hcardT143_33
      (fun i => conj_mem_of_fixedPoints _ _ (T143_33 i) (hfix143_33 i) _)
      ⟨143, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T143_33_2 Q2.hfix143_33_2 Q2.hinj143_33_2
      Q2.hcardT143_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_33_2 i) (Q2.hfix143_33_2 i) _)
      colCert_143_33_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T143_33
      hfix143_33 hinj143_33 hcardT143_33
      (fun i => conj_mem_of_fixedPoints _ _ (T143_33 i) (hfix143_33 i) _)
      ⟨143, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T143_33_2 Q2.hfix143_33_2 Q2.hinj143_33_2
      Q2.hcardT143_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_33_2 i) (Q2.hfix143_33_2 i) _)
      colCert_143_33_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T143_33
      hfix143_33 hinj143_33 hcardT143_33
      (fun i => conj_mem_of_fixedPoints _ _ (T143_33 i) (hfix143_33 i) _)
      ⟨143, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T143_33_2 Q2.hfix143_33_2 Q2.hinj143_33_2
      Q2.hcardT143_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_33_2 i) (Q2.hfix143_33_2 i) _)
      colCert_143_33_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T143_33
      hfix143_33 hinj143_33 hcardT143_33
      (fun i => conj_mem_of_fixedPoints _ _ (T143_33 i) (hfix143_33 i) _)
      ⟨143, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T143_33_2 Q2.hfix143_33_2 Q2.hinj143_33_2
      Q2.hcardT143_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_33_2 i) (Q2.hfix143_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T143_33 = colFn colCertDiv_143_33_5.D1 (m := 5) from colCertDiv_143_33_5.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T143_33_2 = colFn colCertDiv_143_33_5.D2 (m := 5) from colCertDiv_143_33_5.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_33_5_match


theorem leaf_143_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T143_33
      hfix143_33 hinj143_33 hcardT143_33
      (fun i => conj_mem_of_fixedPoints _ _ (T143_33 i) (hfix143_33 i) _)
      ⟨143, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T143_33_2 Q2.hfix143_33_2 Q2.hinj143_33_2
      Q2.hcardT143_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_33_2 i) (Q2.hfix143_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T143_33 = colFn colCertDiv_143_33_10.D1 (m := 5) from colCertDiv_143_33_10.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T143_33_2 = colFn colCertDiv_143_33_10.D2 (m := 5) from colCertDiv_143_33_10.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_33_10_match


theorem leaf_143_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T143_33
      hfix143_33 hinj143_33 hcardT143_33
      (fun i => conj_mem_of_fixedPoints _ _ (T143_33 i) (hfix143_33 i) _)
      ⟨143, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T143_33_2 Q2.hfix143_33_2 Q2.hinj143_33_2
      Q2.hcardT143_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_33_2 i) (Q2.hfix143_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T143_33 = colFn colCertDiv_143_33_15.D1 (m := 5) from colCertDiv_143_33_15.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T143_33_2 = colFn colCertDiv_143_33_15.D2 (m := 5) from colCertDiv_143_33_15.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_33_15_match


theorem leaf_143_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T143_33
      hfix143_33 hinj143_33 hcardT143_33
      (fun i => conj_mem_of_fixedPoints _ _ (T143_33 i) (hfix143_33 i) _)
      ⟨143, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T143_33_2 Q2.hfix143_33_2 Q2.hinj143_33_2
      Q2.hcardT143_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_33_2 i) (Q2.hfix143_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T143_33 = colFn colCertDiv_143_33_20.D1 (m := 5) from colCertDiv_143_33_20.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T143_33_2 = colFn colCertDiv_143_33_20.D2 (m := 5) from colCertDiv_143_33_20.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_33_20_match


theorem leaf_143_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T143_34
      hfix143_34 hinj143_34 hcardT143_34
      (fun i => conj_mem_of_fixedPoints _ _ (T143_34 i) (hfix143_34 i) _)
      ⟨143, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T143_34_2 Q2.hfix143_34_2 Q2.hinj143_34_2
      Q2.hcardT143_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_34_2 i) (Q2.hfix143_34_2 i) _)
      colCert_143_34_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T143_34
      hfix143_34 hinj143_34 hcardT143_34
      (fun i => conj_mem_of_fixedPoints _ _ (T143_34 i) (hfix143_34 i) _)
      ⟨143, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T143_34_2 Q2.hfix143_34_2 Q2.hinj143_34_2
      Q2.hcardT143_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_34_2 i) (Q2.hfix143_34_2 i) _)
      colCert_143_34_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T143_34
      hfix143_34 hinj143_34 hcardT143_34
      (fun i => conj_mem_of_fixedPoints _ _ (T143_34 i) (hfix143_34 i) _)
      ⟨143, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T143_34_2 Q2.hfix143_34_2 Q2.hinj143_34_2
      Q2.hcardT143_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_34_2 i) (Q2.hfix143_34_2 i) _)
      colCert_143_34_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T143_34
      hfix143_34 hinj143_34 hcardT143_34
      (fun i => conj_mem_of_fixedPoints _ _ (T143_34 i) (hfix143_34 i) _)
      ⟨143, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T143_34_2 Q2.hfix143_34_2 Q2.hinj143_34_2
      Q2.hcardT143_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_34_2 i) (Q2.hfix143_34_2 i) _)
      colCert_143_34_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T143_34
      hfix143_34 hinj143_34 hcardT143_34
      (fun i => conj_mem_of_fixedPoints _ _ (T143_34 i) (hfix143_34 i) _)
      ⟨143, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T143_34_2 Q2.hfix143_34_2 Q2.hinj143_34_2
      Q2.hcardT143_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_34_2 i) (Q2.hfix143_34_2 i) _)
      colCert_143_34_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T143_34
      hfix143_34 hinj143_34 hcardT143_34
      (fun i => conj_mem_of_fixedPoints _ _ (T143_34 i) (hfix143_34 i) _)
      ⟨143, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T143_34_2 Q2.hfix143_34_2 Q2.hinj143_34_2
      Q2.hcardT143_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_34_2 i) (Q2.hfix143_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T143_34 = colFn colCertDiv_143_34_5.D1 (m := 5) from colCertDiv_143_34_5.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 5 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T143_34_2 = colFn colCertDiv_143_34_5.D2 (m := 5) from colCertDiv_143_34_5.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_34_5_match


theorem leaf_143_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T143_34
      hfix143_34 hinj143_34 hcardT143_34
      (fun i => conj_mem_of_fixedPoints _ _ (T143_34 i) (hfix143_34 i) _)
      ⟨143, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T143_34_2 Q2.hfix143_34_2 Q2.hinj143_34_2
      Q2.hcardT143_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_34_2 i) (Q2.hfix143_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T143_34 = colFn colCertDiv_143_34_10.D1 (m := 5) from colCertDiv_143_34_10.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 10 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T143_34_2 = colFn colCertDiv_143_34_10.D2 (m := 5) from colCertDiv_143_34_10.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_34_10_match


theorem leaf_143_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T143_34
      hfix143_34 hinj143_34 hcardT143_34
      (fun i => conj_mem_of_fixedPoints _ _ (T143_34 i) (hfix143_34 i) _)
      ⟨143, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T143_34_2 Q2.hfix143_34_2 Q2.hinj143_34_2
      Q2.hcardT143_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_34_2 i) (Q2.hfix143_34_2 i) _)
      colCert_143_34_15.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T143_34
      hfix143_34 hinj143_34 hcardT143_34
      (fun i => conj_mem_of_fixedPoints _ _ (T143_34 i) (hfix143_34 i) _)
      ⟨143, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T143_34_2 Q2.hfix143_34_2 Q2.hinj143_34_2
      Q2.hcardT143_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_34_2 i) (Q2.hfix143_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T143_34 = colFn colCertDiv_143_34_20.D1 (m := 5) from colCertDiv_143_34_20.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 20 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T143_34_2 = colFn colCertDiv_143_34_20.D2 (m := 5) from colCertDiv_143_34_20.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_34_20_match


theorem leaf_143_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T143_35
      hfix143_35 hinj143_35 hcardT143_35
      (fun i => conj_mem_of_fixedPoints _ _ (T143_35 i) (hfix143_35 i) _)
      ⟨143, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T143_35_2 Q2.hfix143_35_2 Q2.hinj143_35_2
      Q2.hcardT143_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_35_2 i) (Q2.hfix143_35_2 i) _)
      colCert_143_35_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T143_35
      hfix143_35 hinj143_35 hcardT143_35
      (fun i => conj_mem_of_fixedPoints _ _ (T143_35 i) (hfix143_35 i) _)
      ⟨143, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T143_35_2 Q2.hfix143_35_2 Q2.hinj143_35_2
      Q2.hcardT143_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_35_2 i) (Q2.hfix143_35_2 i) _)
      colCert_143_35_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T143_35
      hfix143_35 hinj143_35 hcardT143_35
      (fun i => conj_mem_of_fixedPoints _ _ (T143_35 i) (hfix143_35 i) _)
      ⟨143, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T143_35_2 Q2.hfix143_35_2 Q2.hinj143_35_2
      Q2.hcardT143_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_35_2 i) (Q2.hfix143_35_2 i) _)
      colCert_143_35_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T143_35
      hfix143_35 hinj143_35 hcardT143_35
      (fun i => conj_mem_of_fixedPoints _ _ (T143_35 i) (hfix143_35 i) _)
      ⟨143, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T143_35_2 Q2.hfix143_35_2 Q2.hinj143_35_2
      Q2.hcardT143_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_35_2 i) (Q2.hfix143_35_2 i) _)
      colCert_143_35_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T143_35
      hfix143_35 hinj143_35 hcardT143_35
      (fun i => conj_mem_of_fixedPoints _ _ (T143_35 i) (hfix143_35 i) _)
      ⟨143, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T143_35_2 Q2.hfix143_35_2 Q2.hinj143_35_2
      Q2.hcardT143_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_35_2 i) (Q2.hfix143_35_2 i) _)
      colCert_143_35_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T143_35
      hfix143_35 hinj143_35 hcardT143_35
      (fun i => conj_mem_of_fixedPoints _ _ (T143_35 i) (hfix143_35 i) _)
      ⟨143, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T143_35_2 Q2.hfix143_35_2 Q2.hinj143_35_2
      Q2.hcardT143_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_35_2 i) (Q2.hfix143_35_2 i) _)
      colCert_143_35_5.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T143_35
      hfix143_35 hinj143_35 hcardT143_35
      (fun i => conj_mem_of_fixedPoints _ _ (T143_35 i) (hfix143_35 i) _)
      ⟨143, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T143_35_2 Q2.hfix143_35_2 Q2.hinj143_35_2
      Q2.hcardT143_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_35_2 i) (Q2.hfix143_35_2 i) _)
      colCert_143_35_10.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T143_35
      hfix143_35 hinj143_35 hcardT143_35
      (fun i => conj_mem_of_fixedPoints _ _ (T143_35 i) (hfix143_35 i) _)
      ⟨143, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T143_35_2 Q2.hfix143_35_2 Q2.hinj143_35_2
      Q2.hcardT143_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_35_2 i) (Q2.hfix143_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T143_35 = colFn colCertDiv_143_35_15.D1 (m := 5) from colCertDiv_143_35_15.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 15 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T143_35_2 = colFn colCertDiv_143_35_15.D2 (m := 5) from colCertDiv_143_35_15.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_35_15_match


theorem leaf_143_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T143_35
      hfix143_35 hinj143_35 hcardT143_35
      (fun i => conj_mem_of_fixedPoints _ _ (T143_35 i) (hfix143_35 i) _)
      ⟨143, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T143_35_2 Q2.hfix143_35_2 Q2.hinj143_35_2
      Q2.hcardT143_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_35_2 i) (Q2.hfix143_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T143_35 = colFn colCertDiv_143_35_20.D1 (m := 5) from colCertDiv_143_35_20.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 20 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T143_35_2 = colFn colCertDiv_143_35_20.D2 (m := 5) from colCertDiv_143_35_20.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_35_20_match


theorem leaf_143_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T143_36
      hfix143_36 hinj143_36 hcardT143_36
      (fun i => conj_mem_of_fixedPoints _ _ (T143_36 i) (hfix143_36 i) _)
      ⟨143, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T143_36_2 Q2.hfix143_36_2 Q2.hinj143_36_2
      Q2.hcardT143_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_36_2 i) (Q2.hfix143_36_2 i) _)
      colCert_143_36_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T143_36
      hfix143_36 hinj143_36 hcardT143_36
      (fun i => conj_mem_of_fixedPoints _ _ (T143_36 i) (hfix143_36 i) _)
      ⟨143, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T143_36_2 Q2.hfix143_36_2 Q2.hinj143_36_2
      Q2.hcardT143_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_36_2 i) (Q2.hfix143_36_2 i) _)
      colCert_143_36_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T143_36
      hfix143_36 hinj143_36 hcardT143_36
      (fun i => conj_mem_of_fixedPoints _ _ (T143_36 i) (hfix143_36 i) _)
      ⟨143, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T143_36_2 Q2.hfix143_36_2 Q2.hinj143_36_2
      Q2.hcardT143_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_36_2 i) (Q2.hfix143_36_2 i) _)
      colCert_143_36_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T143_36
      hfix143_36 hinj143_36 hcardT143_36
      (fun i => conj_mem_of_fixedPoints _ _ (T143_36 i) (hfix143_36 i) _)
      ⟨143, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T143_36_2 Q2.hfix143_36_2 Q2.hinj143_36_2
      Q2.hcardT143_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_36_2 i) (Q2.hfix143_36_2 i) _)
      colCert_143_36_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T143_36
      hfix143_36 hinj143_36 hcardT143_36
      (fun i => conj_mem_of_fixedPoints _ _ (T143_36 i) (hfix143_36 i) _)
      ⟨143, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T143_36_2 Q2.hfix143_36_2 Q2.hinj143_36_2
      Q2.hcardT143_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_36_2 i) (Q2.hfix143_36_2 i) _)
      colCert_143_36_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T143_36
      hfix143_36 hinj143_36 hcardT143_36
      (fun i => conj_mem_of_fixedPoints _ _ (T143_36 i) (hfix143_36 i) _)
      ⟨143, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T143_36_2 Q2.hfix143_36_2 Q2.hinj143_36_2
      Q2.hcardT143_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_36_2 i) (Q2.hfix143_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T143_36 = colFn colCertDiv_143_36_5.D1 (m := 5) from colCertDiv_143_36_5.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 5 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T143_36_2 = colFn colCertDiv_143_36_5.D2 (m := 5) from colCertDiv_143_36_5.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_36_5_match


theorem leaf_143_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T143_36
      hfix143_36 hinj143_36 hcardT143_36
      (fun i => conj_mem_of_fixedPoints _ _ (T143_36 i) (hfix143_36 i) _)
      ⟨143, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T143_36_2 Q2.hfix143_36_2 Q2.hinj143_36_2
      Q2.hcardT143_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_36_2 i) (Q2.hfix143_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T143_36 = colFn colCertDiv_143_36_10.D1 (m := 5) from colCertDiv_143_36_10.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 10 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T143_36_2 = colFn colCertDiv_143_36_10.D2 (m := 5) from colCertDiv_143_36_10.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_36_10_match


theorem leaf_143_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T143_36
      hfix143_36 hinj143_36 hcardT143_36
      (fun i => conj_mem_of_fixedPoints _ _ (T143_36 i) (hfix143_36 i) _)
      ⟨143, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T143_36_2 Q2.hfix143_36_2 Q2.hinj143_36_2
      Q2.hcardT143_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_36_2 i) (Q2.hfix143_36_2 i) _)
      colCert_143_36_15.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T143_36
      hfix143_36 hinj143_36 hcardT143_36
      (fun i => conj_mem_of_fixedPoints _ _ (T143_36 i) (hfix143_36 i) _)
      ⟨143, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T143_36_2 Q2.hfix143_36_2 Q2.hinj143_36_2
      Q2.hcardT143_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_36_2 i) (Q2.hfix143_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T143_36 = colFn colCertDiv_143_36_20.D1 (m := 5) from colCertDiv_143_36_20.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 20 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T143_36_2 = colFn colCertDiv_143_36_20.D2 (m := 5) from colCertDiv_143_36_20.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_36_20_match


theorem leaf_143_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T143_37
      hfix143_37 hinj143_37 hcardT143_37
      (fun i => conj_mem_of_fixedPoints _ _ (T143_37 i) (hfix143_37 i) _)
      ⟨143, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T143_37_2 Q2.hfix143_37_2 Q2.hinj143_37_2
      Q2.hcardT143_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_37_2 i) (Q2.hfix143_37_2 i) _)
      colCert_143_37_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T143_37
      hfix143_37 hinj143_37 hcardT143_37
      (fun i => conj_mem_of_fixedPoints _ _ (T143_37 i) (hfix143_37 i) _)
      ⟨143, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T143_37_2 Q2.hfix143_37_2 Q2.hinj143_37_2
      Q2.hcardT143_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_37_2 i) (Q2.hfix143_37_2 i) _)
      colCert_143_37_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T143_37
      hfix143_37 hinj143_37 hcardT143_37
      (fun i => conj_mem_of_fixedPoints _ _ (T143_37 i) (hfix143_37 i) _)
      ⟨143, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T143_37_2 Q2.hfix143_37_2 Q2.hinj143_37_2
      Q2.hcardT143_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_37_2 i) (Q2.hfix143_37_2 i) _)
      colCert_143_37_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T143_37
      hfix143_37 hinj143_37 hcardT143_37
      (fun i => conj_mem_of_fixedPoints _ _ (T143_37 i) (hfix143_37 i) _)
      ⟨143, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T143_37_2 Q2.hfix143_37_2 Q2.hinj143_37_2
      Q2.hcardT143_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_37_2 i) (Q2.hfix143_37_2 i) _)
      colCert_143_37_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T143_37
      hfix143_37 hinj143_37 hcardT143_37
      (fun i => conj_mem_of_fixedPoints _ _ (T143_37 i) (hfix143_37 i) _)
      ⟨143, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T143_37_2 Q2.hfix143_37_2 Q2.hinj143_37_2
      Q2.hcardT143_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_37_2 i) (Q2.hfix143_37_2 i) _)
      colCert_143_37_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T143_37
      hfix143_37 hinj143_37 hcardT143_37
      (fun i => conj_mem_of_fixedPoints _ _ (T143_37 i) (hfix143_37 i) _)
      ⟨143, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T143_37_2 Q2.hfix143_37_2 Q2.hinj143_37_2
      Q2.hcardT143_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_37_2 i) (Q2.hfix143_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T143_37 = colFn colCertDiv_143_37_5.D1 (m := 5) from colCertDiv_143_37_5.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T143_37_2 = colFn colCertDiv_143_37_5.D2 (m := 5) from colCertDiv_143_37_5.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_37_5_match


theorem leaf_143_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T143_37
      hfix143_37 hinj143_37 hcardT143_37
      (fun i => conj_mem_of_fixedPoints _ _ (T143_37 i) (hfix143_37 i) _)
      ⟨143, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T143_37_2 Q2.hfix143_37_2 Q2.hinj143_37_2
      Q2.hcardT143_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_37_2 i) (Q2.hfix143_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T143_37 = colFn colCertDiv_143_37_10.D1 (m := 5) from colCertDiv_143_37_10.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T143_37_2 = colFn colCertDiv_143_37_10.D2 (m := 5) from colCertDiv_143_37_10.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_37_10_match


theorem leaf_143_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T143_37
      hfix143_37 hinj143_37 hcardT143_37
      (fun i => conj_mem_of_fixedPoints _ _ (T143_37 i) (hfix143_37 i) _)
      ⟨143, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T143_37_2 Q2.hfix143_37_2 Q2.hinj143_37_2
      Q2.hcardT143_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_37_2 i) (Q2.hfix143_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T143_37 = colFn colCertDiv_143_37_15.D1 (m := 5) from colCertDiv_143_37_15.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T143_37_2 = colFn colCertDiv_143_37_15.D2 (m := 5) from colCertDiv_143_37_15.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_37_15_match


theorem leaf_143_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T143_37
      hfix143_37 hinj143_37 hcardT143_37
      (fun i => conj_mem_of_fixedPoints _ _ (T143_37 i) (hfix143_37 i) _)
      ⟨143, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T143_37_2 Q2.hfix143_37_2 Q2.hinj143_37_2
      Q2.hcardT143_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_37_2 i) (Q2.hfix143_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T143_37 = colFn colCertDiv_143_37_20.D1 (m := 5) from colCertDiv_143_37_20.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T143_37_2 = colFn colCertDiv_143_37_20.D2 (m := 5) from colCertDiv_143_37_20.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_37_20_match


theorem leaf_143_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T143_53
      hfix143_53 hinj143_53 hcardT143_53
      (fun i => conj_mem_of_fixedPoints _ _ (T143_53 i) (hfix143_53 i) _)
      ⟨143, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T143_53_2 Q2.hfix143_53_2 Q2.hinj143_53_2
      Q2.hcardT143_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_53_2 i) (Q2.hfix143_53_2 i) _)
      colCert_143_53_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T143_53
      hfix143_53 hinj143_53 hcardT143_53
      (fun i => conj_mem_of_fixedPoints _ _ (T143_53 i) (hfix143_53 i) _)
      ⟨143, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T143_53_2 Q2.hfix143_53_2 Q2.hinj143_53_2
      Q2.hcardT143_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_53_2 i) (Q2.hfix143_53_2 i) _)
      colCert_143_53_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T143_53
      hfix143_53 hinj143_53 hcardT143_53
      (fun i => conj_mem_of_fixedPoints _ _ (T143_53 i) (hfix143_53 i) _)
      ⟨143, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T143_53_2 Q2.hfix143_53_2 Q2.hinj143_53_2
      Q2.hcardT143_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_53_2 i) (Q2.hfix143_53_2 i) _)
      colCert_143_53_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T143_53
      hfix143_53 hinj143_53 hcardT143_53
      (fun i => conj_mem_of_fixedPoints _ _ (T143_53 i) (hfix143_53 i) _)
      ⟨143, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T143_53_2 Q2.hfix143_53_2 Q2.hinj143_53_2
      Q2.hcardT143_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_53_2 i) (Q2.hfix143_53_2 i) _)
      colCert_143_53_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T143_53
      hfix143_53 hinj143_53 hcardT143_53
      (fun i => conj_mem_of_fixedPoints _ _ (T143_53 i) (hfix143_53 i) _)
      ⟨143, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T143_53_2 Q2.hfix143_53_2 Q2.hinj143_53_2
      Q2.hcardT143_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_53_2 i) (Q2.hfix143_53_2 i) _)
      colCert_143_53_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T143_53
      hfix143_53 hinj143_53 hcardT143_53
      (fun i => conj_mem_of_fixedPoints _ _ (T143_53 i) (hfix143_53 i) _)
      ⟨143, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T143_53_2 Q2.hfix143_53_2 Q2.hinj143_53_2
      Q2.hcardT143_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_53_2 i) (Q2.hfix143_53_2 i) _)
      colCert_143_53_5.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T143_53
      hfix143_53 hinj143_53 hcardT143_53
      (fun i => conj_mem_of_fixedPoints _ _ (T143_53 i) (hfix143_53 i) _)
      ⟨143, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T143_53_2 Q2.hfix143_53_2 Q2.hinj143_53_2
      Q2.hcardT143_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_53_2 i) (Q2.hfix143_53_2 i) _)
      colCert_143_53_10.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T143_53
      hfix143_53 hinj143_53 hcardT143_53
      (fun i => conj_mem_of_fixedPoints _ _ (T143_53 i) (hfix143_53 i) _)
      ⟨143, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T143_53_2 Q2.hfix143_53_2 Q2.hinj143_53_2
      Q2.hcardT143_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_53_2 i) (Q2.hfix143_53_2 i) _)
      colCert_143_53_15.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T143_53
      hfix143_53 hinj143_53 hcardT143_53
      (fun i => conj_mem_of_fixedPoints _ _ (T143_53 i) (hfix143_53 i) _)
      ⟨143, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T143_53_2 Q2.hfix143_53_2 Q2.hinj143_53_2
      Q2.hcardT143_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_53_2 i) (Q2.hfix143_53_2 i) _)
      colCert_143_53_20.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T143_54
      hfix143_54 hinj143_54 hcardT143_54
      (fun i => conj_mem_of_fixedPoints _ _ (T143_54 i) (hfix143_54 i) _)
      ⟨143, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T143_54_2 Q2.hfix143_54_2 Q2.hinj143_54_2
      Q2.hcardT143_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_54_2 i) (Q2.hfix143_54_2 i) _)
      colCert_143_54_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T143_54
      hfix143_54 hinj143_54 hcardT143_54
      (fun i => conj_mem_of_fixedPoints _ _ (T143_54 i) (hfix143_54 i) _)
      ⟨143, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T143_54_2 Q2.hfix143_54_2 Q2.hinj143_54_2
      Q2.hcardT143_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_54_2 i) (Q2.hfix143_54_2 i) _)
      colCert_143_54_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T143_54
      hfix143_54 hinj143_54 hcardT143_54
      (fun i => conj_mem_of_fixedPoints _ _ (T143_54 i) (hfix143_54 i) _)
      ⟨143, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T143_54_2 Q2.hfix143_54_2 Q2.hinj143_54_2
      Q2.hcardT143_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_54_2 i) (Q2.hfix143_54_2 i) _)
      colCert_143_54_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T143_54
      hfix143_54 hinj143_54 hcardT143_54
      (fun i => conj_mem_of_fixedPoints _ _ (T143_54 i) (hfix143_54 i) _)
      ⟨143, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T143_54_2 Q2.hfix143_54_2 Q2.hinj143_54_2
      Q2.hcardT143_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_54_2 i) (Q2.hfix143_54_2 i) _)
      colCert_143_54_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T143_54
      hfix143_54 hinj143_54 hcardT143_54
      (fun i => conj_mem_of_fixedPoints _ _ (T143_54 i) (hfix143_54 i) _)
      ⟨143, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T143_54_2 Q2.hfix143_54_2 Q2.hinj143_54_2
      Q2.hcardT143_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_54_2 i) (Q2.hfix143_54_2 i) _)
      colCert_143_54_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T143_54
      hfix143_54 hinj143_54 hcardT143_54
      (fun i => conj_mem_of_fixedPoints _ _ (T143_54 i) (hfix143_54 i) _)
      ⟨143, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T143_54_2 Q2.hfix143_54_2 Q2.hinj143_54_2
      Q2.hcardT143_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_54_2 i) (Q2.hfix143_54_2 i) _)
      colCert_143_54_5.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T143_54
      hfix143_54 hinj143_54 hcardT143_54
      (fun i => conj_mem_of_fixedPoints _ _ (T143_54 i) (hfix143_54 i) _)
      ⟨143, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T143_54_2 Q2.hfix143_54_2 Q2.hinj143_54_2
      Q2.hcardT143_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_54_2 i) (Q2.hfix143_54_2 i) _)
      colCert_143_54_10.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T143_54
      hfix143_54 hinj143_54 hcardT143_54
      (fun i => conj_mem_of_fixedPoints _ _ (T143_54 i) (hfix143_54 i) _)
      ⟨143, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T143_54_2 Q2.hfix143_54_2 Q2.hinj143_54_2
      Q2.hcardT143_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_54_2 i) (Q2.hfix143_54_2 i) _)
      colCert_143_54_15.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T143_54
      hfix143_54 hinj143_54 hcardT143_54
      (fun i => conj_mem_of_fixedPoints _ _ (T143_54 i) (hfix143_54 i) _)
      ⟨143, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T143_54_2 Q2.hfix143_54_2 Q2.hinj143_54_2
      Q2.hcardT143_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_54_2 i) (Q2.hfix143_54_2 i) _)
      colCert_143_54_20.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_95_0 (hp : 0 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 0 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      colCert_143_95_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_95_1 (hp : 1 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 1 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      colCert_143_95_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_95_2 (hp : 2 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 2 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      colCert_143_95_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_95_3 (hp : 3 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 3 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      colCert_143_95_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_95_4 (hp : 4 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 4 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      colCert_143_95_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_95_5 (hp : 5 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 5 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      colCert_143_95_5.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_95_10 (hp : 10 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 10 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      colCert_143_95_10.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_95_15 (hp : 15 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 15 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      colCert_143_95_15.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_95_20 (hp : 20 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 20 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      colCert_143_95_20.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_95_25 (hp : 25 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 25 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 25 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T143_95 = colFn colCertDiv_143_95_25.D1 (m := 5) from colCertDiv_143_95_25.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 25 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T143_95_2 = colFn colCertDiv_143_95_25.D2 (m := 5) from colCertDiv_143_95_25.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_95_25_match


theorem leaf_143_95_50 (hp : 50 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 50 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 50 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T143_95 = colFn colCertDiv_143_95_50.D1 (m := 5) from colCertDiv_143_95_50.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 50 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T143_95_2 = colFn colCertDiv_143_95_50.D2 (m := 5) from colCertDiv_143_95_50.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_95_50_match


theorem leaf_143_95_75 (hp : 75 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 75 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 75 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T143_95 = colFn colCertDiv_143_95_75.D1 (m := 5) from colCertDiv_143_95_75.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 75 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T143_95_2 = colFn colCertDiv_143_95_75.D2 (m := 5) from colCertDiv_143_95_75.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_95_75_match


theorem leaf_143_95_100 (hp : 100 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 100 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp)) T143_95
      hfix143_95 hinj143_95 hcardT143_95
      (fun i => conj_mem_of_fixedPoints _ _ (T143_95 i) (hfix143_95 i) _)
      ⟨143, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 100 hp) Q2.T143_95_2 Q2.hfix143_95_2 Q2.hinj143_95_2
      Q2.hcardT143_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_95_2 i) (Q2.hfix143_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T143_95 = colFn colCertDiv_143_95_100.D1 (m := 5) from colCertDiv_143_95_100.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 100 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T143_95_2 = colFn colCertDiv_143_95_100.D2 (m := 5) from colCertDiv_143_95_100.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_95_100_match


theorem leaf_143_96_0 (hp : 0 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp)) T143_96
      hfix143_96 hinj143_96 hcardT143_96
      (fun i => conj_mem_of_fixedPoints _ _ (T143_96 i) (hfix143_96 i) _)
      ⟨143, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 0 hp) Q2.T143_96_2 Q2.hfix143_96_2 Q2.hinj143_96_2
      Q2.hcardT143_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_96_2 i) (Q2.hfix143_96_2 i) _)
      colCert_143_96_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_96_1 (hp : 1 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp)) T143_96
      hfix143_96 hinj143_96 hcardT143_96
      (fun i => conj_mem_of_fixedPoints _ _ (T143_96 i) (hfix143_96 i) _)
      ⟨143, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 1 hp) Q2.T143_96_2 Q2.hfix143_96_2 Q2.hinj143_96_2
      Q2.hcardT143_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_96_2 i) (Q2.hfix143_96_2 i) _)
      colCert_143_96_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_96_2 (hp : 2 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp)) T143_96
      hfix143_96 hinj143_96 hcardT143_96
      (fun i => conj_mem_of_fixedPoints _ _ (T143_96 i) (hfix143_96 i) _)
      ⟨143, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 2 hp) Q2.T143_96_2 Q2.hfix143_96_2 Q2.hinj143_96_2
      Q2.hcardT143_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_96_2 i) (Q2.hfix143_96_2 i) _)
      colCert_143_96_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_96_3 (hp : 3 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp)) T143_96
      hfix143_96 hinj143_96 hcardT143_96
      (fun i => conj_mem_of_fixedPoints _ _ (T143_96 i) (hfix143_96 i) _)
      ⟨143, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 3 hp) Q2.T143_96_2 Q2.hfix143_96_2 Q2.hinj143_96_2
      Q2.hcardT143_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_96_2 i) (Q2.hfix143_96_2 i) _)
      colCert_143_96_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_96_4 (hp : 4 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp)) T143_96
      hfix143_96 hinj143_96 hcardT143_96
      (fun i => conj_mem_of_fixedPoints _ _ (T143_96 i) (hfix143_96 i) _)
      ⟨143, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 4 hp) Q2.T143_96_2 Q2.hfix143_96_2 Q2.hinj143_96_2
      Q2.hcardT143_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_96_2 i) (Q2.hfix143_96_2 i) _)
      colCert_143_96_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_96_5 (hp : 5 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp)) T143_96
      hfix143_96 hinj143_96 hcardT143_96
      (fun i => conj_mem_of_fixedPoints _ _ (T143_96 i) (hfix143_96 i) _)
      ⟨143, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 5 hp) Q2.T143_96_2 Q2.hfix143_96_2 Q2.hinj143_96_2
      Q2.hcardT143_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_96_2 i) (Q2.hfix143_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T143_96 = colFn colCertDiv_143_96_5.D1 (m := 5) from colCertDiv_143_96_5.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 5 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T143_96_2 = colFn colCertDiv_143_96_5.D2 (m := 5) from colCertDiv_143_96_5.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_96_5_match


theorem leaf_143_96_10 (hp : 10 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp)) T143_96
      hfix143_96 hinj143_96 hcardT143_96
      (fun i => conj_mem_of_fixedPoints _ _ (T143_96 i) (hfix143_96 i) _)
      ⟨143, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 10 hp) Q2.T143_96_2 Q2.hfix143_96_2 Q2.hinj143_96_2
      Q2.hcardT143_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_96_2 i) (Q2.hfix143_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T143_96 = colFn colCertDiv_143_96_10.D1 (m := 5) from colCertDiv_143_96_10.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 10 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T143_96_2 = colFn colCertDiv_143_96_10.D2 (m := 5) from colCertDiv_143_96_10.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_96_10_match


theorem leaf_143_96_15 (hp : 15 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp)) T143_96
      hfix143_96 hinj143_96 hcardT143_96
      (fun i => conj_mem_of_fixedPoints _ _ (T143_96 i) (hfix143_96 i) _)
      ⟨143, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 15 hp) Q2.T143_96_2 Q2.hfix143_96_2 Q2.hinj143_96_2
      Q2.hcardT143_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_96_2 i) (Q2.hfix143_96_2 i) _)
      colCert_143_96_15.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_96_20 (hp : 20 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp)) T143_96
      hfix143_96 hinj143_96 hcardT143_96
      (fun i => conj_mem_of_fixedPoints _ _ (T143_96 i) (hfix143_96 i) _)
      ⟨143, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 20 hp) Q2.T143_96_2 Q2.hfix143_96_2 Q2.hinj143_96_2
      Q2.hcardT143_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_96_2 i) (Q2.hfix143_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T143_96 = colFn colCertDiv_143_96_20.D1 (m := 5) from colCertDiv_143_96_20.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 20 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T143_96_2 = colFn colCertDiv_143_96_20.D2 (m := 5) from colCertDiv_143_96_20.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_96_20_match


theorem leaf_143_97_0 (hp : 0 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp)) T143_97
      hfix143_97 hinj143_97 hcardT143_97
      (fun i => conj_mem_of_fixedPoints _ _ (T143_97 i) (hfix143_97 i) _)
      ⟨143, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 0 hp) Q2.T143_97_2 Q2.hfix143_97_2 Q2.hinj143_97_2
      Q2.hcardT143_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_97_2 i) (Q2.hfix143_97_2 i) _)
      colCert_143_97_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_97_1 (hp : 1 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp)) T143_97
      hfix143_97 hinj143_97 hcardT143_97
      (fun i => conj_mem_of_fixedPoints _ _ (T143_97 i) (hfix143_97 i) _)
      ⟨143, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 1 hp) Q2.T143_97_2 Q2.hfix143_97_2 Q2.hinj143_97_2
      Q2.hcardT143_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_97_2 i) (Q2.hfix143_97_2 i) _)
      colCert_143_97_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_97_2 (hp : 2 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp)) T143_97
      hfix143_97 hinj143_97 hcardT143_97
      (fun i => conj_mem_of_fixedPoints _ _ (T143_97 i) (hfix143_97 i) _)
      ⟨143, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 2 hp) Q2.T143_97_2 Q2.hfix143_97_2 Q2.hinj143_97_2
      Q2.hcardT143_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_97_2 i) (Q2.hfix143_97_2 i) _)
      colCert_143_97_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_97_3 (hp : 3 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp)) T143_97
      hfix143_97 hinj143_97 hcardT143_97
      (fun i => conj_mem_of_fixedPoints _ _ (T143_97 i) (hfix143_97 i) _)
      ⟨143, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 3 hp) Q2.T143_97_2 Q2.hfix143_97_2 Q2.hinj143_97_2
      Q2.hcardT143_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_97_2 i) (Q2.hfix143_97_2 i) _)
      colCert_143_97_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_97_4 (hp : 4 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp)) T143_97
      hfix143_97 hinj143_97 hcardT143_97
      (fun i => conj_mem_of_fixedPoints _ _ (T143_97 i) (hfix143_97 i) _)
      ⟨143, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 4 hp) Q2.T143_97_2 Q2.hfix143_97_2 Q2.hinj143_97_2
      Q2.hcardT143_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_97_2 i) (Q2.hfix143_97_2 i) _)
      colCert_143_97_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_97_5 (hp : 5 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp)) T143_97
      hfix143_97 hinj143_97 hcardT143_97
      (fun i => conj_mem_of_fixedPoints _ _ (T143_97 i) (hfix143_97 i) _)
      ⟨143, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 5 hp) Q2.T143_97_2 Q2.hfix143_97_2 Q2.hinj143_97_2
      Q2.hcardT143_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_97_2 i) (Q2.hfix143_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T143_97 = colFn colCertDiv_143_97_5.D1 (m := 5) from colCertDiv_143_97_5.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 5 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T143_97_2 = colFn colCertDiv_143_97_5.D2 (m := 5) from colCertDiv_143_97_5.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_97_5_match


theorem leaf_143_97_10 (hp : 10 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp)) T143_97
      hfix143_97 hinj143_97 hcardT143_97
      (fun i => conj_mem_of_fixedPoints _ _ (T143_97 i) (hfix143_97 i) _)
      ⟨143, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 10 hp) Q2.T143_97_2 Q2.hfix143_97_2 Q2.hinj143_97_2
      Q2.hcardT143_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_97_2 i) (Q2.hfix143_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T143_97 = colFn colCertDiv_143_97_10.D1 (m := 5) from colCertDiv_143_97_10.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 10 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T143_97_2 = colFn colCertDiv_143_97_10.D2 (m := 5) from colCertDiv_143_97_10.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_97_10_match


theorem leaf_143_97_15 (hp : 15 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp)) T143_97
      hfix143_97 hinj143_97 hcardT143_97
      (fun i => conj_mem_of_fixedPoints _ _ (T143_97 i) (hfix143_97 i) _)
      ⟨143, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 15 hp) Q2.T143_97_2 Q2.hfix143_97_2 Q2.hinj143_97_2
      Q2.hcardT143_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_97_2 i) (Q2.hfix143_97_2 i) _)
      colCert_143_97_15.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_97_20 (hp : 20 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp)) T143_97
      hfix143_97 hinj143_97 hcardT143_97
      (fun i => conj_mem_of_fixedPoints _ _ (T143_97 i) (hfix143_97 i) _)
      ⟨143, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 20 hp) Q2.T143_97_2 Q2.hfix143_97_2 Q2.hinj143_97_2
      Q2.hcardT143_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_97_2 i) (Q2.hfix143_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T143_97 = colFn colCertDiv_143_97_20.D1 (m := 5) from colCertDiv_143_97_20.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 20 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T143_97_2 = colFn colCertDiv_143_97_20.D2 (m := 5) from colCertDiv_143_97_20.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_97_20_match


theorem leaf_143_98_0 (hp : 0 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp)) T143_98
      hfix143_98 hinj143_98 hcardT143_98
      (fun i => conj_mem_of_fixedPoints _ _ (T143_98 i) (hfix143_98 i) _)
      ⟨143, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 0 hp) Q2.T143_98_2 Q2.hfix143_98_2 Q2.hinj143_98_2
      Q2.hcardT143_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_98_2 i) (Q2.hfix143_98_2 i) _)
      colCert_143_98_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_98_1 (hp : 1 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp)) T143_98
      hfix143_98 hinj143_98 hcardT143_98
      (fun i => conj_mem_of_fixedPoints _ _ (T143_98 i) (hfix143_98 i) _)
      ⟨143, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 1 hp) Q2.T143_98_2 Q2.hfix143_98_2 Q2.hinj143_98_2
      Q2.hcardT143_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_98_2 i) (Q2.hfix143_98_2 i) _)
      colCert_143_98_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_98_2 (hp : 2 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp)) T143_98
      hfix143_98 hinj143_98 hcardT143_98
      (fun i => conj_mem_of_fixedPoints _ _ (T143_98 i) (hfix143_98 i) _)
      ⟨143, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 2 hp) Q2.T143_98_2 Q2.hfix143_98_2 Q2.hinj143_98_2
      Q2.hcardT143_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_98_2 i) (Q2.hfix143_98_2 i) _)
      colCert_143_98_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_98_3 (hp : 3 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp)) T143_98
      hfix143_98 hinj143_98 hcardT143_98
      (fun i => conj_mem_of_fixedPoints _ _ (T143_98 i) (hfix143_98 i) _)
      ⟨143, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 3 hp) Q2.T143_98_2 Q2.hfix143_98_2 Q2.hinj143_98_2
      Q2.hcardT143_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_98_2 i) (Q2.hfix143_98_2 i) _)
      colCert_143_98_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_98_4 (hp : 4 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp)) T143_98
      hfix143_98 hinj143_98 hcardT143_98
      (fun i => conj_mem_of_fixedPoints _ _ (T143_98 i) (hfix143_98 i) _)
      ⟨143, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 4 hp) Q2.T143_98_2 Q2.hfix143_98_2 Q2.hinj143_98_2
      Q2.hcardT143_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_98_2 i) (Q2.hfix143_98_2 i) _)
      colCert_143_98_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_98_5 (hp : 5 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp)) T143_98
      hfix143_98 hinj143_98 hcardT143_98
      (fun i => conj_mem_of_fixedPoints _ _ (T143_98 i) (hfix143_98 i) _)
      ⟨143, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 5 hp) Q2.T143_98_2 Q2.hfix143_98_2 Q2.hinj143_98_2
      Q2.hcardT143_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_98_2 i) (Q2.hfix143_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T143_98 = colFn colCertDiv_143_98_5.D1 (m := 5) from colCertDiv_143_98_5.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 5 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T143_98_2 = colFn colCertDiv_143_98_5.D2 (m := 5) from colCertDiv_143_98_5.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_98_5_match


theorem leaf_143_98_10 (hp : 10 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp)) T143_98
      hfix143_98 hinj143_98 hcardT143_98
      (fun i => conj_mem_of_fixedPoints _ _ (T143_98 i) (hfix143_98 i) _)
      ⟨143, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 10 hp) Q2.T143_98_2 Q2.hfix143_98_2 Q2.hinj143_98_2
      Q2.hcardT143_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_98_2 i) (Q2.hfix143_98_2 i) _)
      colCert_143_98_10.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_98_15 (hp : 15 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp)) T143_98
      hfix143_98 hinj143_98 hcardT143_98
      (fun i => conj_mem_of_fixedPoints _ _ (T143_98 i) (hfix143_98 i) _)
      ⟨143, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 15 hp) Q2.T143_98_2 Q2.hfix143_98_2 Q2.hinj143_98_2
      Q2.hcardT143_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_98_2 i) (Q2.hfix143_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T143_98 = colFn colCertDiv_143_98_15.D1 (m := 5) from colCertDiv_143_98_15.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 15 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T143_98_2 = colFn colCertDiv_143_98_15.D2 (m := 5) from colCertDiv_143_98_15.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_98_15_match


theorem leaf_143_98_20 (hp : 20 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp)) T143_98
      hfix143_98 hinj143_98 hcardT143_98
      (fun i => conj_mem_of_fixedPoints _ _ (T143_98 i) (hfix143_98 i) _)
      ⟨143, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 20 hp) Q2.T143_98_2 Q2.hfix143_98_2 Q2.hinj143_98_2
      Q2.hcardT143_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_98_2 i) (Q2.hfix143_98_2 i) _)
      colCert_143_98_20.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_99_0 (hp : 0 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp)) T143_99
      hfix143_99 hinj143_99 hcardT143_99
      (fun i => conj_mem_of_fixedPoints _ _ (T143_99 i) (hfix143_99 i) _)
      ⟨143, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 0 hp) Q2.T143_99_2 Q2.hfix143_99_2 Q2.hinj143_99_2
      Q2.hcardT143_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_99_2 i) (Q2.hfix143_99_2 i) _)
      colCert_143_99_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_99_1 (hp : 1 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp)) T143_99
      hfix143_99 hinj143_99 hcardT143_99
      (fun i => conj_mem_of_fixedPoints _ _ (T143_99 i) (hfix143_99 i) _)
      ⟨143, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 1 hp) Q2.T143_99_2 Q2.hfix143_99_2 Q2.hinj143_99_2
      Q2.hcardT143_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_99_2 i) (Q2.hfix143_99_2 i) _)
      colCert_143_99_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_99_2 (hp : 2 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp)) T143_99
      hfix143_99 hinj143_99 hcardT143_99
      (fun i => conj_mem_of_fixedPoints _ _ (T143_99 i) (hfix143_99 i) _)
      ⟨143, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 2 hp) Q2.T143_99_2 Q2.hfix143_99_2 Q2.hinj143_99_2
      Q2.hcardT143_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_99_2 i) (Q2.hfix143_99_2 i) _)
      colCert_143_99_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_99_3 (hp : 3 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp)) T143_99
      hfix143_99 hinj143_99 hcardT143_99
      (fun i => conj_mem_of_fixedPoints _ _ (T143_99 i) (hfix143_99 i) _)
      ⟨143, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 3 hp) Q2.T143_99_2 Q2.hfix143_99_2 Q2.hinj143_99_2
      Q2.hcardT143_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_99_2 i) (Q2.hfix143_99_2 i) _)
      colCert_143_99_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_99_4 (hp : 4 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp)) T143_99
      hfix143_99 hinj143_99 hcardT143_99
      (fun i => conj_mem_of_fixedPoints _ _ (T143_99 i) (hfix143_99 i) _)
      ⟨143, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 4 hp) Q2.T143_99_2 Q2.hfix143_99_2 Q2.hinj143_99_2
      Q2.hcardT143_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_99_2 i) (Q2.hfix143_99_2 i) _)
      colCert_143_99_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_99_5 (hp : 5 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp)) T143_99
      hfix143_99 hinj143_99 hcardT143_99
      (fun i => conj_mem_of_fixedPoints _ _ (T143_99 i) (hfix143_99 i) _)
      ⟨143, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 5 hp) Q2.T143_99_2 Q2.hfix143_99_2 Q2.hinj143_99_2
      Q2.hcardT143_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_99_2 i) (Q2.hfix143_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T143_99 = colFn colCertDiv_143_99_5.D1 (m := 5) from colCertDiv_143_99_5.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 5 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T143_99_2 = colFn colCertDiv_143_99_5.D2 (m := 5) from colCertDiv_143_99_5.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_99_5_match


theorem leaf_143_99_10 (hp : 10 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp)) T143_99
      hfix143_99 hinj143_99 hcardT143_99
      (fun i => conj_mem_of_fixedPoints _ _ (T143_99 i) (hfix143_99 i) _)
      ⟨143, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 10 hp) Q2.T143_99_2 Q2.hfix143_99_2 Q2.hinj143_99_2
      Q2.hcardT143_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_99_2 i) (Q2.hfix143_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T143_99 = colFn colCertDiv_143_99_10.D1 (m := 5) from colCertDiv_143_99_10.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 10 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T143_99_2 = colFn colCertDiv_143_99_10.D2 (m := 5) from colCertDiv_143_99_10.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_99_10_match


theorem leaf_143_99_15 (hp : 15 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp)) T143_99
      hfix143_99 hinj143_99 hcardT143_99
      (fun i => conj_mem_of_fixedPoints _ _ (T143_99 i) (hfix143_99 i) _)
      ⟨143, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 15 hp) Q2.T143_99_2 Q2.hfix143_99_2 Q2.hinj143_99_2
      Q2.hcardT143_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_99_2 i) (Q2.hfix143_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T143_99 = colFn colCertDiv_143_99_15.D1 (m := 5) from colCertDiv_143_99_15.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 15 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T143_99_2 = colFn colCertDiv_143_99_15.D2 (m := 5) from colCertDiv_143_99_15.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_99_15_match


theorem leaf_143_99_20 (hp : 20 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨143, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp)) T143_99
      hfix143_99 hinj143_99 hcardT143_99
      (fun i => conj_mem_of_fixedPoints _ _ (T143_99 i) (hfix143_99 i) _)
      ⟨143, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 20 hp) Q2.T143_99_2 Q2.hfix143_99_2 Q2.hinj143_99_2
      Q2.hcardT143_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_99_2 i) (Q2.hfix143_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨143, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T143_99 = colFn colCertDiv_143_99_20.D1 (m := 5) from colCertDiv_143_99_20.bind1,
    show colData2 (⟨143, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 20 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T143_99_2 = colFn colCertDiv_143_99_20.D2 (m := 5) from colCertDiv_143_99_20.bind2]
  rw [alnId_143 j hj]
  exact fastcode_of_div ⟨143, by decide⟩ _ _ _
    ((alnId_143 j hj) ▸ Q2.listedAt (⟨143, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨143, by decide⟩ : Fin 148) hj hq).1) colCertDiv_143_99_20_match


theorem leaf_143_115_0 (hp : 0 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp)) T143_115
      hfix143_115 hinj143_115 hcardT143_115
      (fun i => conj_mem_of_fixedPoints _ _ (T143_115 i) (hfix143_115 i) _)
      ⟨143, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 0 hp) Q2.T143_115_2 Q2.hfix143_115_2 Q2.hinj143_115_2
      Q2.hcardT143_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_115_2 i) (Q2.hfix143_115_2 i) _)
      colCert_143_115_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_115_1 (hp : 1 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp)) T143_115
      hfix143_115 hinj143_115 hcardT143_115
      (fun i => conj_mem_of_fixedPoints _ _ (T143_115 i) (hfix143_115 i) _)
      ⟨143, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 1 hp) Q2.T143_115_2 Q2.hfix143_115_2 Q2.hinj143_115_2
      Q2.hcardT143_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_115_2 i) (Q2.hfix143_115_2 i) _)
      colCert_143_115_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_115_2 (hp : 2 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp)) T143_115
      hfix143_115 hinj143_115 hcardT143_115
      (fun i => conj_mem_of_fixedPoints _ _ (T143_115 i) (hfix143_115 i) _)
      ⟨143, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 2 hp) Q2.T143_115_2 Q2.hfix143_115_2 Q2.hinj143_115_2
      Q2.hcardT143_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_115_2 i) (Q2.hfix143_115_2 i) _)
      colCert_143_115_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_115_3 (hp : 3 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp)) T143_115
      hfix143_115 hinj143_115 hcardT143_115
      (fun i => conj_mem_of_fixedPoints _ _ (T143_115 i) (hfix143_115 i) _)
      ⟨143, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 3 hp) Q2.T143_115_2 Q2.hfix143_115_2 Q2.hinj143_115_2
      Q2.hcardT143_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_115_2 i) (Q2.hfix143_115_2 i) _)
      colCert_143_115_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_115_4 (hp : 4 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp)) T143_115
      hfix143_115 hinj143_115 hcardT143_115
      (fun i => conj_mem_of_fixedPoints _ _ (T143_115 i) (hfix143_115 i) _)
      ⟨143, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 4 hp) Q2.T143_115_2 Q2.hfix143_115_2 Q2.hinj143_115_2
      Q2.hcardT143_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_115_2 i) (Q2.hfix143_115_2 i) _)
      colCert_143_115_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_115_5 (hp : 5 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp)) T143_115
      hfix143_115 hinj143_115 hcardT143_115
      (fun i => conj_mem_of_fixedPoints _ _ (T143_115 i) (hfix143_115 i) _)
      ⟨143, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 5 hp) Q2.T143_115_2 Q2.hfix143_115_2 Q2.hinj143_115_2
      Q2.hcardT143_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_115_2 i) (Q2.hfix143_115_2 i) _)
      colCert_143_115_5.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_115_10 (hp : 10 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp)) T143_115
      hfix143_115 hinj143_115 hcardT143_115
      (fun i => conj_mem_of_fixedPoints _ _ (T143_115 i) (hfix143_115 i) _)
      ⟨143, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 10 hp) Q2.T143_115_2 Q2.hfix143_115_2 Q2.hinj143_115_2
      Q2.hcardT143_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_115_2 i) (Q2.hfix143_115_2 i) _)
      colCert_143_115_10.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_115_15 (hp : 15 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp)) T143_115
      hfix143_115 hinj143_115 hcardT143_115
      (fun i => conj_mem_of_fixedPoints _ _ (T143_115 i) (hfix143_115 i) _)
      ⟨143, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 15 hp) Q2.T143_115_2 Q2.hfix143_115_2 Q2.hinj143_115_2
      Q2.hcardT143_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_115_2 i) (Q2.hfix143_115_2 i) _)
      colCert_143_115_15.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_115_20 (hp : 20 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp)) T143_115
      hfix143_115 hinj143_115 hcardT143_115
      (fun i => conj_mem_of_fixedPoints _ _ (T143_115 i) (hfix143_115 i) _)
      ⟨143, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 20 hp) Q2.T143_115_2 Q2.hfix143_115_2 Q2.hinj143_115_2
      Q2.hcardT143_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_115_2 i) (Q2.hfix143_115_2 i) _)
      colCert_143_115_20.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_0 (hp : 0 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 0 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 0 (transLenTr ⟨143, by decide⟩ 0 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 0 (transLenTr ⟨143, by decide⟩ 0 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 0 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_0.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_1 (hp : 1 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 1 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 1 (transLenTr ⟨143, by decide⟩ 1 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 1 (transLenTr ⟨143, by decide⟩ 1 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 1 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_1.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_2 (hp : 2 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 2 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 2 (transLenTr ⟨143, by decide⟩ 2 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 2 (transLenTr ⟨143, by decide⟩ 2 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 2 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_2.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_3 (hp : 3 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 3 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 3 (transLenTr ⟨143, by decide⟩ 3 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 3 (transLenTr ⟨143, by decide⟩ 3 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 3 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_3.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_4 (hp : 4 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 4 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 4 (transLenTr ⟨143, by decide⟩ 4 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 4 (transLenTr ⟨143, by decide⟩ 4 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 4 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_4.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_5 (hp : 5 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 5 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 5 (transLenTr ⟨143, by decide⟩ 5 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 5 (transLenTr ⟨143, by decide⟩ 5 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 5 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_5.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_6 (hp : 6 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 6 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 6 (transLenTr ⟨143, by decide⟩ 6 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 6 (transLenTr ⟨143, by decide⟩ 6 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 6 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_6.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_7 (hp : 7 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 7 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 7 (transLenTr ⟨143, by decide⟩ 7 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 7 (transLenTr ⟨143, by decide⟩ 7 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 7 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_7.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_8 (hp : 8 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 8 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 8 (transLenTr ⟨143, by decide⟩ 8 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 8 (transLenTr ⟨143, by decide⟩ 8 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 8 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_8.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_9 (hp : 9 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 9 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 9 (transLenTr ⟨143, by decide⟩ 9 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 9 (transLenTr ⟨143, by decide⟩ 9 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 9 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_9.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_10 (hp : 10 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 10 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 10 (transLenTr ⟨143, by decide⟩ 10 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 10 (transLenTr ⟨143, by decide⟩ 10 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 10 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_10.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_11 (hp : 11 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 11 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 11 (transLenTr ⟨143, by decide⟩ 11 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 11 (transLenTr ⟨143, by decide⟩ 11 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 11 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_11.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_12 (hp : 12 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 12 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 12 (transLenTr ⟨143, by decide⟩ 12 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 12 (transLenTr ⟨143, by decide⟩ 12 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 12 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_12.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_13 (hp : 13 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 13 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 13 (transLenTr ⟨143, by decide⟩ 13 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 13 (transLenTr ⟨143, by decide⟩ 13 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 13 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_13.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_14 (hp : 14 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 14 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 14 (transLenTr ⟨143, by decide⟩ 14 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 14 (transLenTr ⟨143, by decide⟩ 14 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 14 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_14.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_15 (hp : 15 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 15 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 15 (transLenTr ⟨143, by decide⟩ 15 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 15 (transLenTr ⟨143, by decide⟩ 15 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 15 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_15.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_16 (hp : 16 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 16 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 16 (transLenTr ⟨143, by decide⟩ 16 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 16 (transLenTr ⟨143, by decide⟩ 16 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 16 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_16.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_17 (hp : 17 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 17 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 17 (transLenTr ⟨143, by decide⟩ 17 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 17 (transLenTr ⟨143, by decide⟩ 17 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 17 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_17.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_18 (hp : 18 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 18 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 18 (transLenTr ⟨143, by decide⟩ 18 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 18 (transLenTr ⟨143, by decide⟩ 18 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 18 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_18.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_19 (hp : 19 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 19 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 19 (transLenTr ⟨143, by decide⟩ 19 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 19 (transLenTr ⟨143, by decide⟩ 19 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 19 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_19.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_20 (hp : 20 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 20 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 20 (transLenTr ⟨143, by decide⟩ 20 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 20 (transLenTr ⟨143, by decide⟩ 20 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 20 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_20.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_21 (hp : 21 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 21 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 21 (transLenTr ⟨143, by decide⟩ 21 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 21 (transLenTr ⟨143, by decide⟩ 21 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 21 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_21.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_22 (hp : 22 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 22 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 22 (transLenTr ⟨143, by decide⟩ 22 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 22 (transLenTr ⟨143, by decide⟩ 22 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 22 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_22.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_23 (hp : 23 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 23 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 23 (transLenTr ⟨143, by decide⟩ 23 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 23 (transLenTr ⟨143, by decide⟩ 23 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 23 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_23.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_143_143_24 (hp : 24 < (Q2.transData.getD 143 []).length)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ 24 hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ 24 (transLenTr ⟨143, by decide⟩ 24 hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨143, by decide⟩ : Fin 148) ⟨143, by decide⟩ _
      (validAt ⟨143, by decide⟩ (listedAt ⟨143, by decide⟩ hj))
      (colE1 ⟨143, by decide⟩ 24 (transLenTr ⟨143, by decide⟩ 24 hp)) T143_143
      hfix143_143 hinj143_143 hcardT143_143
      (fun i => conj_mem_of_fixedPoints _ _ (T143_143 i) (hfix143_143 i) _)
      ⟨143, by decide⟩ ⟨143, by decide⟩ _
      (Q2.validAt ⟨143, by decide⟩ (Q2.listedAt ⟨143, by decide⟩
        (alnCheck_rep ⟨143, by decide⟩ hj hq).1))
      (colE2 ⟨143, by decide⟩ 24 hp) Q2.T143_143_2 Q2.hfix143_143_2 Q2.hinj143_143_2
      Q2.hcardT143_143_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T143_143_2 i) (Q2.hfix143_143_2 i) _)
      colCert_143_143_24.hD ?_).symm
  rw [alnId_143 j hj]


theorem leaf_144_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T144_10
      hfix144_10 hinj144_10 hcardT144_10
      (fun i => conj_mem_of_fixedPoints _ _ (T144_10 i) (hfix144_10 i) _)
      ⟨144, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T144_10_2 Q2.hfix144_10_2 Q2.hinj144_10_2
      Q2.hcardT144_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_10_2 i) (Q2.hfix144_10_2 i) _)
      colCert_144_10_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T144_10
      hfix144_10 hinj144_10 hcardT144_10
      (fun i => conj_mem_of_fixedPoints _ _ (T144_10 i) (hfix144_10 i) _)
      ⟨144, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T144_10_2 Q2.hfix144_10_2 Q2.hinj144_10_2
      Q2.hcardT144_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_10_2 i) (Q2.hfix144_10_2 i) _)
      colCert_144_10_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T144_10
      hfix144_10 hinj144_10 hcardT144_10
      (fun i => conj_mem_of_fixedPoints _ _ (T144_10 i) (hfix144_10 i) _)
      ⟨144, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T144_10_2 Q2.hfix144_10_2 Q2.hinj144_10_2
      Q2.hcardT144_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_10_2 i) (Q2.hfix144_10_2 i) _)
      colCert_144_10_2.hD ?_).symm
  rw [alnId_144 j hj]


end LeanDring.P5Presentation
