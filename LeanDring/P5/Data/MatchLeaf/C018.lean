/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C041
import LeanDring.P5.Data.ColRestCheap.C190
import LeanDring.P5.Data.ColRestCheap.C191
import LeanDring.P5.Data.ColRestCheap.C192
import LeanDring.P5.Data.ColRestCheap.C193
import LeanDring.P5.Data.ColRestCheap.C194
import LeanDring.P5.Data.EntryK.C021
import LeanDring.P5.Data.EntryK.C022
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesAlign.C022
import LeanDring.P5.Data.SpeciesAlign.C023
import LeanDring.P5.Data.SpeciesAlign.C024
import LeanDring.P5.Data.SpeciesDiv.C054
import LeanDring.P5.Data.SpeciesDiv.C055

/-! # Stage-5 leaves, chunk 17 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_89_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T89_54
      hfix89_54 hinj89_54 hcardT89_54
      (fun i => conj_mem_of_fixedPoints _ _ (T89_54 i) (hfix89_54 i) _)
      ⟨89, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T89_54_2 Q2.hfix89_54_2 Q2.hinj89_54_2
      Q2.hcardT89_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_54_2 i) (Q2.hfix89_54_2 i) _)
      colCert_89_54_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T89_54
      hfix89_54 hinj89_54 hcardT89_54
      (fun i => conj_mem_of_fixedPoints _ _ (T89_54 i) (hfix89_54 i) _)
      ⟨89, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T89_54_2 Q2.hfix89_54_2 Q2.hinj89_54_2
      Q2.hcardT89_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_54_2 i) (Q2.hfix89_54_2 i) _)
      colCert_89_54_5.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T89_54
      hfix89_54 hinj89_54 hcardT89_54
      (fun i => conj_mem_of_fixedPoints _ _ (T89_54 i) (hfix89_54 i) _)
      ⟨89, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T89_54_2 Q2.hfix89_54_2 Q2.hinj89_54_2
      Q2.hcardT89_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_54_2 i) (Q2.hfix89_54_2 i) _)
      colCert_89_54_10.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T89_54
      hfix89_54 hinj89_54 hcardT89_54
      (fun i => conj_mem_of_fixedPoints _ _ (T89_54 i) (hfix89_54 i) _)
      ⟨89, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T89_54_2 Q2.hfix89_54_2 Q2.hinj89_54_2
      Q2.hcardT89_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_54_2 i) (Q2.hfix89_54_2 i) _)
      colCert_89_54_15.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T89_54
      hfix89_54 hinj89_54 hcardT89_54
      (fun i => conj_mem_of_fixedPoints _ _ (T89_54 i) (hfix89_54 i) _)
      ⟨89, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T89_54_2 Q2.hfix89_54_2 Q2.hinj89_54_2
      Q2.hcardT89_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_54_2 i) (Q2.hfix89_54_2 i) _)
      colCert_89_54_20.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_0 (hp : 0 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 0 (transLenTr ⟨89, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 0 (transLenTr ⟨89, by decide⟩ 0 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 0 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_1 (hp : 1 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 1 (transLenTr ⟨89, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 1 (transLenTr ⟨89, by decide⟩ 1 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 1 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_2 (hp : 2 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 2 (transLenTr ⟨89, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 2 (transLenTr ⟨89, by decide⟩ 2 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 2 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_3 (hp : 3 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 3 (transLenTr ⟨89, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 3 (transLenTr ⟨89, by decide⟩ 3 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 3 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_4 (hp : 4 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 4 (transLenTr ⟨89, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 4 (transLenTr ⟨89, by decide⟩ 4 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 4 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_5 (hp : 5 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 5 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 5 (transLenTr ⟨89, by decide⟩ 5 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 5 (transLenTr ⟨89, by decide⟩ 5 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 5 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_5.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_6 (hp : 6 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 6 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 6 (transLenTr ⟨89, by decide⟩ 6 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 6 (transLenTr ⟨89, by decide⟩ 6 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 6 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_6.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_7 (hp : 7 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 7 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 7 (transLenTr ⟨89, by decide⟩ 7 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 7 (transLenTr ⟨89, by decide⟩ 7 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 7 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_7.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_8 (hp : 8 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 8 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 8 (transLenTr ⟨89, by decide⟩ 8 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 8 (transLenTr ⟨89, by decide⟩ 8 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 8 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_8.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_9 (hp : 9 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 9 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 9 (transLenTr ⟨89, by decide⟩ 9 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 9 (transLenTr ⟨89, by decide⟩ 9 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 9 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_9.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_10 (hp : 10 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 10 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 10 (transLenTr ⟨89, by decide⟩ 10 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 10 (transLenTr ⟨89, by decide⟩ 10 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 10 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_10.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_11 (hp : 11 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 11 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 11 (transLenTr ⟨89, by decide⟩ 11 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 11 (transLenTr ⟨89, by decide⟩ 11 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 11 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_11.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_12 (hp : 12 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 12 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 12 (transLenTr ⟨89, by decide⟩ 12 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 12 (transLenTr ⟨89, by decide⟩ 12 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 12 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_12.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_13 (hp : 13 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 13 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 13 (transLenTr ⟨89, by decide⟩ 13 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 13 (transLenTr ⟨89, by decide⟩ 13 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 13 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_13.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_14 (hp : 14 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 14 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 14 (transLenTr ⟨89, by decide⟩ 14 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 14 (transLenTr ⟨89, by decide⟩ 14 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 14 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_14.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_15 (hp : 15 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 15 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 15 (transLenTr ⟨89, by decide⟩ 15 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 15 (transLenTr ⟨89, by decide⟩ 15 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 15 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_15.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_16 (hp : 16 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 16 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 16 (transLenTr ⟨89, by decide⟩ 16 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 16 (transLenTr ⟨89, by decide⟩ 16 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 16 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_16.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_17 (hp : 17 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 17 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 17 (transLenTr ⟨89, by decide⟩ 17 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 17 (transLenTr ⟨89, by decide⟩ 17 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 17 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_17.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_18 (hp : 18 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 18 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 18 (transLenTr ⟨89, by decide⟩ 18 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 18 (transLenTr ⟨89, by decide⟩ 18 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 18 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_18.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_19 (hp : 19 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 19 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 19 (transLenTr ⟨89, by decide⟩ 19 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 19 (transLenTr ⟨89, by decide⟩ 19 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 19 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_19.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_20 (hp : 20 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 20 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 20 (transLenTr ⟨89, by decide⟩ 20 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 20 (transLenTr ⟨89, by decide⟩ 20 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 20 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_20.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_21 (hp : 21 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 21 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 21 (transLenTr ⟨89, by decide⟩ 21 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 21 (transLenTr ⟨89, by decide⟩ 21 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 21 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_21.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_22 (hp : 22 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 22 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 22 (transLenTr ⟨89, by decide⟩ 22 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 22 (transLenTr ⟨89, by decide⟩ 22 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 22 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_22.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_23 (hp : 23 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 23 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 23 (transLenTr ⟨89, by decide⟩ 23 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 23 (transLenTr ⟨89, by decide⟩ 23 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 23 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_23.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_89_24 (hp : 24 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 24 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 24 (transLenTr ⟨89, by decide⟩ 24 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 24 (transLenTr ⟨89, by decide⟩ 24 hp)) T89_89
      hfix89_89 hinj89_89 hcardT89_89
      (fun i => conj_mem_of_fixedPoints _ _ (T89_89 i) (hfix89_89 i) _)
      ⟨89, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 24 hp) Q2.T89_89_2 Q2.hfix89_89_2 Q2.hinj89_89_2
      Q2.hcardT89_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_89_2 i) (Q2.hfix89_89_2 i) _)
      colCert_89_89_24.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_90_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T90_10
      hfix90_10 hinj90_10 hcardT90_10
      (fun i => conj_mem_of_fixedPoints _ _ (T90_10 i) (hfix90_10 i) _)
      ⟨90, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T90_10_2 Q2.hfix90_10_2 Q2.hinj90_10_2
      Q2.hcardT90_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_10_2 i) (Q2.hfix90_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T90_10 = colFn colCert_90_10_0.D (m := 25) from colCert_90_10_0.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 0 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T90_10_2 = colFn colCert_90_10_0.D (m := 25) from colCert_90_10_0.bind2]
  exact alnAll_90_10_0 j hj hq

theorem leaf_90_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T90_10
      hfix90_10 hinj90_10 hcardT90_10
      (fun i => conj_mem_of_fixedPoints _ _ (T90_10 i) (hfix90_10 i) _)
      ⟨90, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T90_10_2 Q2.hfix90_10_2 Q2.hinj90_10_2
      Q2.hcardT90_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_10_2 i) (Q2.hfix90_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T90_10 = colFn colCert_90_10_1.D (m := 25) from colCert_90_10_1.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 1 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T90_10_2 = colFn colCert_90_10_1.D (m := 25) from colCert_90_10_1.bind2]
  exact alnAll_90_10_1 j hj hq

theorem leaf_90_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T90_10
      hfix90_10 hinj90_10 hcardT90_10
      (fun i => conj_mem_of_fixedPoints _ _ (T90_10 i) (hfix90_10 i) _)
      ⟨90, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T90_10_2 Q2.hfix90_10_2 Q2.hinj90_10_2
      Q2.hcardT90_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_10_2 i) (Q2.hfix90_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T90_10 = colFn colCert_90_10_2.D (m := 25) from colCert_90_10_2.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 2 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T90_10_2 = colFn colCert_90_10_2.D (m := 25) from colCert_90_10_2.bind2]
  exact alnAll_90_10_2 j hj hq

theorem leaf_90_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T90_10
      hfix90_10 hinj90_10 hcardT90_10
      (fun i => conj_mem_of_fixedPoints _ _ (T90_10 i) (hfix90_10 i) _)
      ⟨90, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T90_10_2 Q2.hfix90_10_2 Q2.hinj90_10_2
      Q2.hcardT90_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_10_2 i) (Q2.hfix90_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T90_10 = colFn colCert_90_10_3.D (m := 25) from colCert_90_10_3.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 3 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T90_10_2 = colFn colCert_90_10_3.D (m := 25) from colCert_90_10_3.bind2]
  exact alnAll_90_10_3 j hj hq

theorem leaf_90_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T90_10
      hfix90_10 hinj90_10 hcardT90_10
      (fun i => conj_mem_of_fixedPoints _ _ (T90_10 i) (hfix90_10 i) _)
      ⟨90, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T90_10_2 Q2.hfix90_10_2 Q2.hinj90_10_2
      Q2.hcardT90_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_10_2 i) (Q2.hfix90_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T90_10 = colFn colCert_90_10_4.D (m := 25) from colCert_90_10_4.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 4 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T90_10_2 = colFn colCert_90_10_4.D (m := 25) from colCert_90_10_4.bind2]
  exact alnAll_90_10_4 j hj hq

theorem leaf_90_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T90_12
      hfix90_12 hinj90_12 hcardT90_12
      (fun i => conj_mem_of_fixedPoints _ _ (T90_12 i) (hfix90_12 i) _)
      ⟨90, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T90_12_2 Q2.hfix90_12_2 Q2.hinj90_12_2
      Q2.hcardT90_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_12_2 i) (Q2.hfix90_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T90_12 = colFn colCert_90_12_0.D (m := 25) from colCert_90_12_0.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T90_12_2 = colFn colCert_90_12_0.D (m := 25) from colCert_90_12_0.bind2]
  exact alnAll_90_12_0 j hj hq

theorem leaf_90_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T90_12
      hfix90_12 hinj90_12 hcardT90_12
      (fun i => conj_mem_of_fixedPoints _ _ (T90_12 i) (hfix90_12 i) _)
      ⟨90, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T90_12_2 Q2.hfix90_12_2 Q2.hinj90_12_2
      Q2.hcardT90_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_12_2 i) (Q2.hfix90_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T90_12 = colFn colCert_90_12_1.D (m := 25) from colCert_90_12_1.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T90_12_2 = colFn colCert_90_12_1.D (m := 25) from colCert_90_12_1.bind2]
  exact alnAll_90_12_1 j hj hq

theorem leaf_90_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T90_12
      hfix90_12 hinj90_12 hcardT90_12
      (fun i => conj_mem_of_fixedPoints _ _ (T90_12 i) (hfix90_12 i) _)
      ⟨90, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T90_12_2 Q2.hfix90_12_2 Q2.hinj90_12_2
      Q2.hcardT90_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_12_2 i) (Q2.hfix90_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T90_12 = colFn colCert_90_12_2.D (m := 25) from colCert_90_12_2.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T90_12_2 = colFn colCert_90_12_2.D (m := 25) from colCert_90_12_2.bind2]
  exact alnAll_90_12_2 j hj hq

theorem leaf_90_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T90_12
      hfix90_12 hinj90_12 hcardT90_12
      (fun i => conj_mem_of_fixedPoints _ _ (T90_12 i) (hfix90_12 i) _)
      ⟨90, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T90_12_2 Q2.hfix90_12_2 Q2.hinj90_12_2
      Q2.hcardT90_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_12_2 i) (Q2.hfix90_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T90_12 = colFn colCert_90_12_3.D (m := 25) from colCert_90_12_3.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T90_12_2 = colFn colCert_90_12_3.D (m := 25) from colCert_90_12_3.bind2]
  exact alnAll_90_12_3 j hj hq

theorem leaf_90_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T90_12
      hfix90_12 hinj90_12 hcardT90_12
      (fun i => conj_mem_of_fixedPoints _ _ (T90_12 i) (hfix90_12 i) _)
      ⟨90, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T90_12_2 Q2.hfix90_12_2 Q2.hinj90_12_2
      Q2.hcardT90_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_12_2 i) (Q2.hfix90_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T90_12 = colFn colCert_90_12_4.D (m := 25) from colCert_90_12_4.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T90_12_2 = colFn colCert_90_12_4.D (m := 25) from colCert_90_12_4.bind2]
  exact alnAll_90_12_4 j hj hq

theorem leaf_90_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T90_28
      hfix90_28 hinj90_28 hcardT90_28
      (fun i => conj_mem_of_fixedPoints _ _ (T90_28 i) (hfix90_28 i) _)
      ⟨90, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T90_28_2 Q2.hfix90_28_2 Q2.hinj90_28_2
      Q2.hcardT90_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_28_2 i) (Q2.hfix90_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T90_28 = colFn colCert_90_28_0.D (m := 25) from colCert_90_28_0.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 0 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T90_28_2 = colFn colCert_90_28_0.D (m := 25) from colCert_90_28_0.bind2]
  exact alnAll_90_28_0 j hj hq

theorem leaf_90_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T90_28
      hfix90_28 hinj90_28 hcardT90_28
      (fun i => conj_mem_of_fixedPoints _ _ (T90_28 i) (hfix90_28 i) _)
      ⟨90, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T90_28_2 Q2.hfix90_28_2 Q2.hinj90_28_2
      Q2.hcardT90_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_28_2 i) (Q2.hfix90_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T90_28 = colFn colCert_90_28_1.D (m := 25) from colCert_90_28_1.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 1 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T90_28_2 = colFn colCert_90_28_1.D (m := 25) from colCert_90_28_1.bind2]
  exact alnAll_90_28_1 j hj hq

theorem leaf_90_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T90_28
      hfix90_28 hinj90_28 hcardT90_28
      (fun i => conj_mem_of_fixedPoints _ _ (T90_28 i) (hfix90_28 i) _)
      ⟨90, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T90_28_2 Q2.hfix90_28_2 Q2.hinj90_28_2
      Q2.hcardT90_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_28_2 i) (Q2.hfix90_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T90_28 = colFn colCert_90_28_2.D (m := 25) from colCert_90_28_2.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 2 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T90_28_2 = colFn colCert_90_28_2.D (m := 25) from colCert_90_28_2.bind2]
  exact alnAll_90_28_2 j hj hq

theorem leaf_90_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T90_28
      hfix90_28 hinj90_28 hcardT90_28
      (fun i => conj_mem_of_fixedPoints _ _ (T90_28 i) (hfix90_28 i) _)
      ⟨90, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T90_28_2 Q2.hfix90_28_2 Q2.hinj90_28_2
      Q2.hcardT90_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_28_2 i) (Q2.hfix90_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T90_28 = colFn colCert_90_28_3.D (m := 25) from colCert_90_28_3.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 3 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T90_28_2 = colFn colCert_90_28_3.D (m := 25) from colCert_90_28_3.bind2]
  exact alnAll_90_28_3 j hj hq

theorem leaf_90_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T90_28
      hfix90_28 hinj90_28 hcardT90_28
      (fun i => conj_mem_of_fixedPoints _ _ (T90_28 i) (hfix90_28 i) _)
      ⟨90, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T90_28_2 Q2.hfix90_28_2 Q2.hinj90_28_2
      Q2.hcardT90_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_28_2 i) (Q2.hfix90_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T90_28 = colFn colCert_90_28_4.D (m := 25) from colCert_90_28_4.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 4 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T90_28_2 = colFn colCert_90_28_4.D (m := 25) from colCert_90_28_4.bind2]
  exact alnAll_90_28_4 j hj hq

theorem leaf_90_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T90_28
      hfix90_28 hinj90_28 hcardT90_28
      (fun i => conj_mem_of_fixedPoints _ _ (T90_28 i) (hfix90_28 i) _)
      ⟨90, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T90_28_2 Q2.hfix90_28_2 Q2.hinj90_28_2
      Q2.hcardT90_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_28_2 i) (Q2.hfix90_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T90_28 = colFn colCertDiv_90_28_5.D1 (m := 25) from colCertDiv_90_28_5.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 5 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T90_28_2 = colFn colCertDiv_90_28_5.D2 (m := 25) from colCertDiv_90_28_5.bind2]
  exact alnAll_90_28_5 j hj hq

theorem leaf_90_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T90_28
      hfix90_28 hinj90_28 hcardT90_28
      (fun i => conj_mem_of_fixedPoints _ _ (T90_28 i) (hfix90_28 i) _)
      ⟨90, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T90_28_2 Q2.hfix90_28_2 Q2.hinj90_28_2
      Q2.hcardT90_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_28_2 i) (Q2.hfix90_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T90_28 = colFn colCertDiv_90_28_10.D1 (m := 25) from colCertDiv_90_28_10.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 10 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T90_28_2 = colFn colCertDiv_90_28_10.D2 (m := 25) from colCertDiv_90_28_10.bind2]
  exact alnAll_90_28_10 j hj hq

theorem leaf_90_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T90_28
      hfix90_28 hinj90_28 hcardT90_28
      (fun i => conj_mem_of_fixedPoints _ _ (T90_28 i) (hfix90_28 i) _)
      ⟨90, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T90_28_2 Q2.hfix90_28_2 Q2.hinj90_28_2
      Q2.hcardT90_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_28_2 i) (Q2.hfix90_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T90_28 = colFn colCertDiv_90_28_15.D1 (m := 25) from colCertDiv_90_28_15.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 15 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T90_28_2 = colFn colCertDiv_90_28_15.D2 (m := 25) from colCertDiv_90_28_15.bind2]
  exact alnAll_90_28_15 j hj hq

theorem leaf_90_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T90_28
      hfix90_28 hinj90_28 hcardT90_28
      (fun i => conj_mem_of_fixedPoints _ _ (T90_28 i) (hfix90_28 i) _)
      ⟨90, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T90_28_2 Q2.hfix90_28_2 Q2.hinj90_28_2
      Q2.hcardT90_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_28_2 i) (Q2.hfix90_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T90_28 = colFn colCertDiv_90_28_20.D1 (m := 25) from colCertDiv_90_28_20.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 20 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T90_28_2 = colFn colCertDiv_90_28_20.D2 (m := 25) from colCertDiv_90_28_20.bind2]
  exact alnAll_90_28_20 j hj hq

theorem leaf_90_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T90_53
      hfix90_53 hinj90_53 hcardT90_53
      (fun i => conj_mem_of_fixedPoints _ _ (T90_53 i) (hfix90_53 i) _)
      ⟨90, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T90_53_2 Q2.hfix90_53_2 Q2.hinj90_53_2
      Q2.hcardT90_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_53_2 i) (Q2.hfix90_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T90_53 = colFn colCert_90_53_0.D (m := 25) from colCert_90_53_0.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 0 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T90_53_2 = colFn colCert_90_53_0.D (m := 25) from colCert_90_53_0.bind2]
  exact alnAll_90_53_0 j hj hq

theorem leaf_90_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T90_53
      hfix90_53 hinj90_53 hcardT90_53
      (fun i => conj_mem_of_fixedPoints _ _ (T90_53 i) (hfix90_53 i) _)
      ⟨90, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T90_53_2 Q2.hfix90_53_2 Q2.hinj90_53_2
      Q2.hcardT90_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_53_2 i) (Q2.hfix90_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T90_53 = colFn colCert_90_53_1.D (m := 25) from colCert_90_53_1.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 1 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T90_53_2 = colFn colCert_90_53_1.D (m := 25) from colCert_90_53_1.bind2]
  exact alnAll_90_53_1 j hj hq

theorem leaf_90_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T90_53
      hfix90_53 hinj90_53 hcardT90_53
      (fun i => conj_mem_of_fixedPoints _ _ (T90_53 i) (hfix90_53 i) _)
      ⟨90, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T90_53_2 Q2.hfix90_53_2 Q2.hinj90_53_2
      Q2.hcardT90_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_53_2 i) (Q2.hfix90_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T90_53 = colFn colCert_90_53_2.D (m := 25) from colCert_90_53_2.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 2 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T90_53_2 = colFn colCert_90_53_2.D (m := 25) from colCert_90_53_2.bind2]
  exact alnAll_90_53_2 j hj hq

theorem leaf_90_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T90_53
      hfix90_53 hinj90_53 hcardT90_53
      (fun i => conj_mem_of_fixedPoints _ _ (T90_53 i) (hfix90_53 i) _)
      ⟨90, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T90_53_2 Q2.hfix90_53_2 Q2.hinj90_53_2
      Q2.hcardT90_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_53_2 i) (Q2.hfix90_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T90_53 = colFn colCert_90_53_3.D (m := 25) from colCert_90_53_3.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 3 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T90_53_2 = colFn colCert_90_53_3.D (m := 25) from colCert_90_53_3.bind2]
  exact alnAll_90_53_3 j hj hq

theorem leaf_90_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T90_53
      hfix90_53 hinj90_53 hcardT90_53
      (fun i => conj_mem_of_fixedPoints _ _ (T90_53 i) (hfix90_53 i) _)
      ⟨90, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T90_53_2 Q2.hfix90_53_2 Q2.hinj90_53_2
      Q2.hcardT90_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_53_2 i) (Q2.hfix90_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T90_53 = colFn colCert_90_53_4.D (m := 25) from colCert_90_53_4.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 4 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T90_53_2 = colFn colCert_90_53_4.D (m := 25) from colCert_90_53_4.bind2]
  exact alnAll_90_53_4 j hj hq

theorem leaf_90_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T90_53
      hfix90_53 hinj90_53 hcardT90_53
      (fun i => conj_mem_of_fixedPoints _ _ (T90_53 i) (hfix90_53 i) _)
      ⟨90, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T90_53_2 Q2.hfix90_53_2 Q2.hinj90_53_2
      Q2.hcardT90_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_53_2 i) (Q2.hfix90_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T90_53 = colFn colCert_90_53_5.D (m := 25) from colCert_90_53_5.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 5 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T90_53_2 = colFn colCert_90_53_5.D (m := 25) from colCert_90_53_5.bind2]
  exact alnAll_90_53_5 j hj hq

theorem leaf_90_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T90_53
      hfix90_53 hinj90_53 hcardT90_53
      (fun i => conj_mem_of_fixedPoints _ _ (T90_53 i) (hfix90_53 i) _)
      ⟨90, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T90_53_2 Q2.hfix90_53_2 Q2.hinj90_53_2
      Q2.hcardT90_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_53_2 i) (Q2.hfix90_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T90_53 = colFn colCert_90_53_10.D (m := 25) from colCert_90_53_10.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 10 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T90_53_2 = colFn colCert_90_53_10.D (m := 25) from colCert_90_53_10.bind2]
  exact alnAll_90_53_10 j hj hq

theorem leaf_90_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T90_53
      hfix90_53 hinj90_53 hcardT90_53
      (fun i => conj_mem_of_fixedPoints _ _ (T90_53 i) (hfix90_53 i) _)
      ⟨90, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T90_53_2 Q2.hfix90_53_2 Q2.hinj90_53_2
      Q2.hcardT90_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_53_2 i) (Q2.hfix90_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T90_53 = colFn colCert_90_53_15.D (m := 25) from colCert_90_53_15.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 15 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T90_53_2 = colFn colCert_90_53_15.D (m := 25) from colCert_90_53_15.bind2]
  exact alnAll_90_53_15 j hj hq

theorem leaf_90_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T90_53
      hfix90_53 hinj90_53 hcardT90_53
      (fun i => conj_mem_of_fixedPoints _ _ (T90_53 i) (hfix90_53 i) _)
      ⟨90, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T90_53_2 Q2.hfix90_53_2 Q2.hinj90_53_2
      Q2.hcardT90_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_53_2 i) (Q2.hfix90_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T90_53 = colFn colCert_90_53_20.D (m := 25) from colCert_90_53_20.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 20 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T90_53_2 = colFn colCert_90_53_20.D (m := 25) from colCert_90_53_20.bind2]
  exact alnAll_90_53_20 j hj hq

theorem leaf_90_90_0 (hp : 0 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 0 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 0 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_0.D (m := 25) from colCert_90_90_0.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 0 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_0.D (m := 25) from colCert_90_90_0.bind2]
  exact alnAll_90_90_0 j hj hq

theorem leaf_90_90_1 (hp : 1 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 1 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 1 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_1.D (m := 25) from colCert_90_90_1.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 1 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_1.D (m := 25) from colCert_90_90_1.bind2]
  exact alnAll_90_90_1 j hj hq

theorem leaf_90_90_2 (hp : 2 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 2 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 2 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_2.D (m := 25) from colCert_90_90_2.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 2 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_2.D (m := 25) from colCert_90_90_2.bind2]
  exact alnAll_90_90_2 j hj hq

theorem leaf_90_90_3 (hp : 3 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 3 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 3 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_3.D (m := 25) from colCert_90_90_3.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 3 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_3.D (m := 25) from colCert_90_90_3.bind2]
  exact alnAll_90_90_3 j hj hq

theorem leaf_90_90_4 (hp : 4 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 4 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 4 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_4.D (m := 25) from colCert_90_90_4.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 4 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_4.D (m := 25) from colCert_90_90_4.bind2]
  exact alnAll_90_90_4 j hj hq

theorem leaf_90_90_5 (hp : 5 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 5 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 5 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_5.D (m := 25) from colCert_90_90_5.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 5 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_5.D (m := 25) from colCert_90_90_5.bind2]
  exact alnAll_90_90_5 j hj hq

theorem leaf_90_90_10 (hp : 10 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 10 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 10 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_10.D (m := 25) from colCert_90_90_10.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 10 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_10.D (m := 25) from colCert_90_90_10.bind2]
  exact alnAll_90_90_10 j hj hq

theorem leaf_90_90_15 (hp : 15 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 15 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 15 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_15.D (m := 25) from colCert_90_90_15.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 15 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_15.D (m := 25) from colCert_90_90_15.bind2]
  exact alnAll_90_90_15 j hj hq

theorem leaf_90_90_20 (hp : 20 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 20 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 20 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_20.D (m := 25) from colCert_90_90_20.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 20 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_20.D (m := 25) from colCert_90_90_20.bind2]
  exact alnAll_90_90_20 j hj hq

theorem leaf_90_90_25 (hp : 25 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 25 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 25 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_25.D (m := 25) from colCert_90_90_25.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 25 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_25.D (m := 25) from colCert_90_90_25.bind2]
  exact alnAll_90_90_25 j hj hq

theorem leaf_90_90_50 (hp : 50 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 50 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 50 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_50.D (m := 25) from colCert_90_90_50.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 50 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_50.D (m := 25) from colCert_90_90_50.bind2]
  exact alnAll_90_90_50 j hj hq

theorem leaf_90_90_75 (hp : 75 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 75 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 75 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_75.D (m := 25) from colCert_90_90_75.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 75 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_75.D (m := 25) from colCert_90_90_75.bind2]
  exact alnAll_90_90_75 j hj hq

theorem leaf_90_90_100 (hp : 100 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 90 []).length)
    (hq : (normIsRep.getD 90 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 100 hp)
        (rowE2 (⟨90, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp))
        (rowE1 (⟨90, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨90, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨90, by decide⟩ (listedAt ⟨90, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp)) T90_90
      hfix90_90 hinj90_90 hcardT90_90
      (fun i => conj_mem_of_fixedPoints _ _ (T90_90 i) (hfix90_90 i) _)
      ⟨90, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨90, by decide⟩ (Q2.listedAt ⟨90, by decide⟩
        (alnCheck_rep ⟨90, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 100 hp) Q2.T90_90_2 Q2.hfix90_90_2 Q2.hinj90_90_2
      Q2.hcardT90_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T90_90_2 i) (Q2.hfix90_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨90, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T90_90 = colFn colCert_90_90_100.D (m := 25) from colCert_90_90_100.bind1,
    show colData2 (⟨90, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 100 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T90_90_2 = colFn colCert_90_90_100.D (m := 25) from colCert_90_90_100.bind2]
  exact alnAll_90_90_100 j hj hq

theorem leaf_91_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T91_10
      hfix91_10 hinj91_10 hcardT91_10
      (fun i => conj_mem_of_fixedPoints _ _ (T91_10 i) (hfix91_10 i) _)
      ⟨91, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T91_10_2 Q2.hfix91_10_2 Q2.hinj91_10_2
      Q2.hcardT91_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_10_2 i) (Q2.hfix91_10_2 i) _)
      colCert_91_10_0.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T91_10
      hfix91_10 hinj91_10 hcardT91_10
      (fun i => conj_mem_of_fixedPoints _ _ (T91_10 i) (hfix91_10 i) _)
      ⟨91, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T91_10_2 Q2.hfix91_10_2 Q2.hinj91_10_2
      Q2.hcardT91_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_10_2 i) (Q2.hfix91_10_2 i) _)
      colCert_91_10_1.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T91_10
      hfix91_10 hinj91_10 hcardT91_10
      (fun i => conj_mem_of_fixedPoints _ _ (T91_10 i) (hfix91_10 i) _)
      ⟨91, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T91_10_2 Q2.hfix91_10_2 Q2.hinj91_10_2
      Q2.hcardT91_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_10_2 i) (Q2.hfix91_10_2 i) _)
      colCert_91_10_2.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T91_10
      hfix91_10 hinj91_10 hcardT91_10
      (fun i => conj_mem_of_fixedPoints _ _ (T91_10 i) (hfix91_10 i) _)
      ⟨91, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T91_10_2 Q2.hfix91_10_2 Q2.hinj91_10_2
      Q2.hcardT91_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_10_2 i) (Q2.hfix91_10_2 i) _)
      colCert_91_10_3.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T91_10
      hfix91_10 hinj91_10 hcardT91_10
      (fun i => conj_mem_of_fixedPoints _ _ (T91_10 i) (hfix91_10 i) _)
      ⟨91, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T91_10_2 Q2.hfix91_10_2 Q2.hinj91_10_2
      Q2.hcardT91_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_10_2 i) (Q2.hfix91_10_2 i) _)
      colCert_91_10_4.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T91_12
      hfix91_12 hinj91_12 hcardT91_12
      (fun i => conj_mem_of_fixedPoints _ _ (T91_12 i) (hfix91_12 i) _)
      ⟨91, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T91_12_2 Q2.hfix91_12_2 Q2.hinj91_12_2
      Q2.hcardT91_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_12_2 i) (Q2.hfix91_12_2 i) _)
      colCert_91_12_0.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T91_12
      hfix91_12 hinj91_12 hcardT91_12
      (fun i => conj_mem_of_fixedPoints _ _ (T91_12 i) (hfix91_12 i) _)
      ⟨91, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T91_12_2 Q2.hfix91_12_2 Q2.hinj91_12_2
      Q2.hcardT91_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_12_2 i) (Q2.hfix91_12_2 i) _)
      colCert_91_12_1.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T91_12
      hfix91_12 hinj91_12 hcardT91_12
      (fun i => conj_mem_of_fixedPoints _ _ (T91_12 i) (hfix91_12 i) _)
      ⟨91, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T91_12_2 Q2.hfix91_12_2 Q2.hinj91_12_2
      Q2.hcardT91_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_12_2 i) (Q2.hfix91_12_2 i) _)
      colCert_91_12_2.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T91_12
      hfix91_12 hinj91_12 hcardT91_12
      (fun i => conj_mem_of_fixedPoints _ _ (T91_12 i) (hfix91_12 i) _)
      ⟨91, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T91_12_2 Q2.hfix91_12_2 Q2.hinj91_12_2
      Q2.hcardT91_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_12_2 i) (Q2.hfix91_12_2 i) _)
      colCert_91_12_3.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T91_12
      hfix91_12 hinj91_12 hcardT91_12
      (fun i => conj_mem_of_fixedPoints _ _ (T91_12 i) (hfix91_12 i) _)
      ⟨91, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T91_12_2 Q2.hfix91_12_2 Q2.hinj91_12_2
      Q2.hcardT91_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_12_2 i) (Q2.hfix91_12_2 i) _)
      colCert_91_12_4.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T91_29
      hfix91_29 hinj91_29 hcardT91_29
      (fun i => conj_mem_of_fixedPoints _ _ (T91_29 i) (hfix91_29 i) _)
      ⟨91, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T91_29_2 Q2.hfix91_29_2 Q2.hinj91_29_2
      Q2.hcardT91_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_29_2 i) (Q2.hfix91_29_2 i) _)
      colCert_91_29_0.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T91_29
      hfix91_29 hinj91_29 hcardT91_29
      (fun i => conj_mem_of_fixedPoints _ _ (T91_29 i) (hfix91_29 i) _)
      ⟨91, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T91_29_2 Q2.hfix91_29_2 Q2.hinj91_29_2
      Q2.hcardT91_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_29_2 i) (Q2.hfix91_29_2 i) _)
      colCert_91_29_1.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T91_29
      hfix91_29 hinj91_29 hcardT91_29
      (fun i => conj_mem_of_fixedPoints _ _ (T91_29 i) (hfix91_29 i) _)
      ⟨91, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T91_29_2 Q2.hfix91_29_2 Q2.hinj91_29_2
      Q2.hcardT91_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_29_2 i) (Q2.hfix91_29_2 i) _)
      colCert_91_29_2.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T91_29
      hfix91_29 hinj91_29 hcardT91_29
      (fun i => conj_mem_of_fixedPoints _ _ (T91_29 i) (hfix91_29 i) _)
      ⟨91, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T91_29_2 Q2.hfix91_29_2 Q2.hinj91_29_2
      Q2.hcardT91_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_29_2 i) (Q2.hfix91_29_2 i) _)
      colCert_91_29_3.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T91_29
      hfix91_29 hinj91_29 hcardT91_29
      (fun i => conj_mem_of_fixedPoints _ _ (T91_29 i) (hfix91_29 i) _)
      ⟨91, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T91_29_2 Q2.hfix91_29_2 Q2.hinj91_29_2
      Q2.hcardT91_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_29_2 i) (Q2.hfix91_29_2 i) _)
      colCert_91_29_4.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T91_29
      hfix91_29 hinj91_29 hcardT91_29
      (fun i => conj_mem_of_fixedPoints _ _ (T91_29 i) (hfix91_29 i) _)
      ⟨91, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T91_29_2 Q2.hfix91_29_2 Q2.hinj91_29_2
      Q2.hcardT91_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_29_2 i) (Q2.hfix91_29_2 i) _)
      colCert_91_29_5.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T91_29
      hfix91_29 hinj91_29 hcardT91_29
      (fun i => conj_mem_of_fixedPoints _ _ (T91_29 i) (hfix91_29 i) _)
      ⟨91, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T91_29_2 Q2.hfix91_29_2 Q2.hinj91_29_2
      Q2.hcardT91_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_29_2 i) (Q2.hfix91_29_2 i) _)
      colCert_91_29_10.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T91_29
      hfix91_29 hinj91_29 hcardT91_29
      (fun i => conj_mem_of_fixedPoints _ _ (T91_29 i) (hfix91_29 i) _)
      ⟨91, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T91_29_2 Q2.hfix91_29_2 Q2.hinj91_29_2
      Q2.hcardT91_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_29_2 i) (Q2.hfix91_29_2 i) _)
      colCert_91_29_15.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T91_29
      hfix91_29 hinj91_29 hcardT91_29
      (fun i => conj_mem_of_fixedPoints _ _ (T91_29 i) (hfix91_29 i) _)
      ⟨91, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T91_29_2 Q2.hfix91_29_2 Q2.hinj91_29_2
      Q2.hcardT91_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_29_2 i) (Q2.hfix91_29_2 i) _)
      colCert_91_29_20.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T91_53
      hfix91_53 hinj91_53 hcardT91_53
      (fun i => conj_mem_of_fixedPoints _ _ (T91_53 i) (hfix91_53 i) _)
      ⟨91, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T91_53_2 Q2.hfix91_53_2 Q2.hinj91_53_2
      Q2.hcardT91_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_53_2 i) (Q2.hfix91_53_2 i) _)
      colCert_91_53_0.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T91_53
      hfix91_53 hinj91_53 hcardT91_53
      (fun i => conj_mem_of_fixedPoints _ _ (T91_53 i) (hfix91_53 i) _)
      ⟨91, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T91_53_2 Q2.hfix91_53_2 Q2.hinj91_53_2
      Q2.hcardT91_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_53_2 i) (Q2.hfix91_53_2 i) _)
      colCert_91_53_1.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T91_53
      hfix91_53 hinj91_53 hcardT91_53
      (fun i => conj_mem_of_fixedPoints _ _ (T91_53 i) (hfix91_53 i) _)
      ⟨91, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T91_53_2 Q2.hfix91_53_2 Q2.hinj91_53_2
      Q2.hcardT91_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_53_2 i) (Q2.hfix91_53_2 i) _)
      colCert_91_53_2.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T91_53
      hfix91_53 hinj91_53 hcardT91_53
      (fun i => conj_mem_of_fixedPoints _ _ (T91_53 i) (hfix91_53 i) _)
      ⟨91, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T91_53_2 Q2.hfix91_53_2 Q2.hinj91_53_2
      Q2.hcardT91_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_53_2 i) (Q2.hfix91_53_2 i) _)
      colCert_91_53_3.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T91_53
      hfix91_53 hinj91_53 hcardT91_53
      (fun i => conj_mem_of_fixedPoints _ _ (T91_53 i) (hfix91_53 i) _)
      ⟨91, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T91_53_2 Q2.hfix91_53_2 Q2.hinj91_53_2
      Q2.hcardT91_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_53_2 i) (Q2.hfix91_53_2 i) _)
      colCert_91_53_4.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T91_53
      hfix91_53 hinj91_53 hcardT91_53
      (fun i => conj_mem_of_fixedPoints _ _ (T91_53 i) (hfix91_53 i) _)
      ⟨91, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T91_53_2 Q2.hfix91_53_2 Q2.hinj91_53_2
      Q2.hcardT91_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_53_2 i) (Q2.hfix91_53_2 i) _)
      colCert_91_53_5.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T91_53
      hfix91_53 hinj91_53 hcardT91_53
      (fun i => conj_mem_of_fixedPoints _ _ (T91_53 i) (hfix91_53 i) _)
      ⟨91, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T91_53_2 Q2.hfix91_53_2 Q2.hinj91_53_2
      Q2.hcardT91_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_53_2 i) (Q2.hfix91_53_2 i) _)
      colCert_91_53_10.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T91_53
      hfix91_53 hinj91_53 hcardT91_53
      (fun i => conj_mem_of_fixedPoints _ _ (T91_53 i) (hfix91_53 i) _)
      ⟨91, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T91_53_2 Q2.hfix91_53_2 Q2.hinj91_53_2
      Q2.hcardT91_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_53_2 i) (Q2.hfix91_53_2 i) _)
      colCert_91_53_15.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T91_53
      hfix91_53 hinj91_53 hcardT91_53
      (fun i => conj_mem_of_fixedPoints _ _ (T91_53 i) (hfix91_53 i) _)
      ⟨91, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T91_53_2 Q2.hfix91_53_2 Q2.hinj91_53_2
      Q2.hcardT91_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_53_2 i) (Q2.hfix91_53_2 i) _)
      colCert_91_53_20.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_91_0 (hp : 0 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 0 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp)) T91_91
      hfix91_91 hinj91_91 hcardT91_91
      (fun i => conj_mem_of_fixedPoints _ _ (T91_91 i) (hfix91_91 i) _)
      ⟨91, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 0 hp) Q2.T91_91_2 Q2.hfix91_91_2 Q2.hinj91_91_2
      Q2.hcardT91_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_91_2 i) (Q2.hfix91_91_2 i) _)
      colCert_91_91_0.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_91_1 (hp : 1 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 1 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp)) T91_91
      hfix91_91 hinj91_91 hcardT91_91
      (fun i => conj_mem_of_fixedPoints _ _ (T91_91 i) (hfix91_91 i) _)
      ⟨91, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 1 hp) Q2.T91_91_2 Q2.hfix91_91_2 Q2.hinj91_91_2
      Q2.hcardT91_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_91_2 i) (Q2.hfix91_91_2 i) _)
      colCert_91_91_1.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_91_2 (hp : 2 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 2 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp)) T91_91
      hfix91_91 hinj91_91 hcardT91_91
      (fun i => conj_mem_of_fixedPoints _ _ (T91_91 i) (hfix91_91 i) _)
      ⟨91, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 2 hp) Q2.T91_91_2 Q2.hfix91_91_2 Q2.hinj91_91_2
      Q2.hcardT91_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_91_2 i) (Q2.hfix91_91_2 i) _)
      colCert_91_91_2.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_91_3 (hp : 3 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 3 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp)) T91_91
      hfix91_91 hinj91_91 hcardT91_91
      (fun i => conj_mem_of_fixedPoints _ _ (T91_91 i) (hfix91_91 i) _)
      ⟨91, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 3 hp) Q2.T91_91_2 Q2.hfix91_91_2 Q2.hinj91_91_2
      Q2.hcardT91_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_91_2 i) (Q2.hfix91_91_2 i) _)
      colCert_91_91_3.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_91_4 (hp : 4 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 4 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp)) T91_91
      hfix91_91 hinj91_91 hcardT91_91
      (fun i => conj_mem_of_fixedPoints _ _ (T91_91 i) (hfix91_91 i) _)
      ⟨91, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 4 hp) Q2.T91_91_2 Q2.hfix91_91_2 Q2.hinj91_91_2
      Q2.hcardT91_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_91_2 i) (Q2.hfix91_91_2 i) _)
      colCert_91_91_4.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_91_5 (hp : 5 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 5 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp)) T91_91
      hfix91_91 hinj91_91 hcardT91_91
      (fun i => conj_mem_of_fixedPoints _ _ (T91_91 i) (hfix91_91 i) _)
      ⟨91, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 5 hp) Q2.T91_91_2 Q2.hfix91_91_2 Q2.hinj91_91_2
      Q2.hcardT91_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_91_2 i) (Q2.hfix91_91_2 i) _)
      colCert_91_91_5.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_91_10 (hp : 10 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 10 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp)) T91_91
      hfix91_91 hinj91_91 hcardT91_91
      (fun i => conj_mem_of_fixedPoints _ _ (T91_91 i) (hfix91_91 i) _)
      ⟨91, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 10 hp) Q2.T91_91_2 Q2.hfix91_91_2 Q2.hinj91_91_2
      Q2.hcardT91_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_91_2 i) (Q2.hfix91_91_2 i) _)
      colCert_91_91_10.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_91_15 (hp : 15 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 15 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp)) T91_91
      hfix91_91 hinj91_91 hcardT91_91
      (fun i => conj_mem_of_fixedPoints _ _ (T91_91 i) (hfix91_91 i) _)
      ⟨91, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 15 hp) Q2.T91_91_2 Q2.hfix91_91_2 Q2.hinj91_91_2
      Q2.hcardT91_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_91_2 i) (Q2.hfix91_91_2 i) _)
      colCert_91_91_15.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_91_91_20 (hp : 20 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 91 []).length)
    (hq : (normIsRep.getD 91 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 20 hp)
        (rowE2 (⟨91, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp))
        (rowE1 (⟨91, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨91, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨91, by decide⟩ (listedAt ⟨91, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp)) T91_91
      hfix91_91 hinj91_91 hcardT91_91
      (fun i => conj_mem_of_fixedPoints _ _ (T91_91 i) (hfix91_91 i) _)
      ⟨91, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨91, by decide⟩ (Q2.listedAt ⟨91, by decide⟩
        (alnCheck_rep ⟨91, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 20 hp) Q2.T91_91_2 Q2.hfix91_91_2 Q2.hinj91_91_2
      Q2.hcardT91_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T91_91_2 i) (Q2.hfix91_91_2 i) _)
      colCert_91_91_20.hD ?_).symm
  rw [alnId_91 j hj]


theorem leaf_92_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T92_10
      hfix92_10 hinj92_10 hcardT92_10
      (fun i => conj_mem_of_fixedPoints _ _ (T92_10 i) (hfix92_10 i) _)
      ⟨92, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T92_10_2 Q2.hfix92_10_2 Q2.hinj92_10_2
      Q2.hcardT92_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_10_2 i) (Q2.hfix92_10_2 i) _)
      colCert_92_10_0.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T92_10
      hfix92_10 hinj92_10 hcardT92_10
      (fun i => conj_mem_of_fixedPoints _ _ (T92_10 i) (hfix92_10 i) _)
      ⟨92, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T92_10_2 Q2.hfix92_10_2 Q2.hinj92_10_2
      Q2.hcardT92_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_10_2 i) (Q2.hfix92_10_2 i) _)
      colCert_92_10_1.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T92_10
      hfix92_10 hinj92_10 hcardT92_10
      (fun i => conj_mem_of_fixedPoints _ _ (T92_10 i) (hfix92_10 i) _)
      ⟨92, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T92_10_2 Q2.hfix92_10_2 Q2.hinj92_10_2
      Q2.hcardT92_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_10_2 i) (Q2.hfix92_10_2 i) _)
      colCert_92_10_2.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T92_10
      hfix92_10 hinj92_10 hcardT92_10
      (fun i => conj_mem_of_fixedPoints _ _ (T92_10 i) (hfix92_10 i) _)
      ⟨92, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T92_10_2 Q2.hfix92_10_2 Q2.hinj92_10_2
      Q2.hcardT92_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_10_2 i) (Q2.hfix92_10_2 i) _)
      colCert_92_10_3.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T92_10
      hfix92_10 hinj92_10 hcardT92_10
      (fun i => conj_mem_of_fixedPoints _ _ (T92_10 i) (hfix92_10 i) _)
      ⟨92, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T92_10_2 Q2.hfix92_10_2 Q2.hinj92_10_2
      Q2.hcardT92_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_10_2 i) (Q2.hfix92_10_2 i) _)
      colCert_92_10_4.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T92_12
      hfix92_12 hinj92_12 hcardT92_12
      (fun i => conj_mem_of_fixedPoints _ _ (T92_12 i) (hfix92_12 i) _)
      ⟨92, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T92_12_2 Q2.hfix92_12_2 Q2.hinj92_12_2
      Q2.hcardT92_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_12_2 i) (Q2.hfix92_12_2 i) _)
      colCert_92_12_0.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T92_12
      hfix92_12 hinj92_12 hcardT92_12
      (fun i => conj_mem_of_fixedPoints _ _ (T92_12 i) (hfix92_12 i) _)
      ⟨92, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T92_12_2 Q2.hfix92_12_2 Q2.hinj92_12_2
      Q2.hcardT92_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_12_2 i) (Q2.hfix92_12_2 i) _)
      colCert_92_12_1.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T92_12
      hfix92_12 hinj92_12 hcardT92_12
      (fun i => conj_mem_of_fixedPoints _ _ (T92_12 i) (hfix92_12 i) _)
      ⟨92, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T92_12_2 Q2.hfix92_12_2 Q2.hinj92_12_2
      Q2.hcardT92_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_12_2 i) (Q2.hfix92_12_2 i) _)
      colCert_92_12_2.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T92_12
      hfix92_12 hinj92_12 hcardT92_12
      (fun i => conj_mem_of_fixedPoints _ _ (T92_12 i) (hfix92_12 i) _)
      ⟨92, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T92_12_2 Q2.hfix92_12_2 Q2.hinj92_12_2
      Q2.hcardT92_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_12_2 i) (Q2.hfix92_12_2 i) _)
      colCert_92_12_3.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T92_12
      hfix92_12 hinj92_12 hcardT92_12
      (fun i => conj_mem_of_fixedPoints _ _ (T92_12 i) (hfix92_12 i) _)
      ⟨92, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T92_12_2 Q2.hfix92_12_2 Q2.hinj92_12_2
      Q2.hcardT92_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_12_2 i) (Q2.hfix92_12_2 i) _)
      colCert_92_12_4.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T92_30
      hfix92_30 hinj92_30 hcardT92_30
      (fun i => conj_mem_of_fixedPoints _ _ (T92_30 i) (hfix92_30 i) _)
      ⟨92, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T92_30_2 Q2.hfix92_30_2 Q2.hinj92_30_2
      Q2.hcardT92_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_30_2 i) (Q2.hfix92_30_2 i) _)
      colCert_92_30_0.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T92_30
      hfix92_30 hinj92_30 hcardT92_30
      (fun i => conj_mem_of_fixedPoints _ _ (T92_30 i) (hfix92_30 i) _)
      ⟨92, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T92_30_2 Q2.hfix92_30_2 Q2.hinj92_30_2
      Q2.hcardT92_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_30_2 i) (Q2.hfix92_30_2 i) _)
      colCert_92_30_1.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T92_30
      hfix92_30 hinj92_30 hcardT92_30
      (fun i => conj_mem_of_fixedPoints _ _ (T92_30 i) (hfix92_30 i) _)
      ⟨92, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T92_30_2 Q2.hfix92_30_2 Q2.hinj92_30_2
      Q2.hcardT92_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_30_2 i) (Q2.hfix92_30_2 i) _)
      colCert_92_30_2.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T92_30
      hfix92_30 hinj92_30 hcardT92_30
      (fun i => conj_mem_of_fixedPoints _ _ (T92_30 i) (hfix92_30 i) _)
      ⟨92, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T92_30_2 Q2.hfix92_30_2 Q2.hinj92_30_2
      Q2.hcardT92_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_30_2 i) (Q2.hfix92_30_2 i) _)
      colCert_92_30_3.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T92_30
      hfix92_30 hinj92_30 hcardT92_30
      (fun i => conj_mem_of_fixedPoints _ _ (T92_30 i) (hfix92_30 i) _)
      ⟨92, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T92_30_2 Q2.hfix92_30_2 Q2.hinj92_30_2
      Q2.hcardT92_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_30_2 i) (Q2.hfix92_30_2 i) _)
      colCert_92_30_4.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨92, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T92_30
      hfix92_30 hinj92_30 hcardT92_30
      (fun i => conj_mem_of_fixedPoints _ _ (T92_30 i) (hfix92_30 i) _)
      ⟨92, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T92_30_2 Q2.hfix92_30_2 Q2.hinj92_30_2
      Q2.hcardT92_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_30_2 i) (Q2.hfix92_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨92, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T92_30 = colFn colCertDiv_92_30_5.D1 (m := 25) from colCertDiv_92_30_5.bind1,
    show colData2 (⟨92, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 5 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T92_30_2 = colFn colCertDiv_92_30_5.D2 (m := 25) from colCertDiv_92_30_5.bind2]
  rw [alnId_92 j hj]
  exact fastcode_of_div ⟨92, by decide⟩ _ _ _
    ((alnId_92 j hj) ▸ Q2.listedAt (⟨92, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨92, by decide⟩ : Fin 148) hj hq).1) colCertDiv_92_30_5_match


theorem leaf_92_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨92, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T92_30
      hfix92_30 hinj92_30 hcardT92_30
      (fun i => conj_mem_of_fixedPoints _ _ (T92_30 i) (hfix92_30 i) _)
      ⟨92, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T92_30_2 Q2.hfix92_30_2 Q2.hinj92_30_2
      Q2.hcardT92_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_30_2 i) (Q2.hfix92_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨92, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T92_30 = colFn colCertDiv_92_30_10.D1 (m := 25) from colCertDiv_92_30_10.bind1,
    show colData2 (⟨92, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 10 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T92_30_2 = colFn colCertDiv_92_30_10.D2 (m := 25) from colCertDiv_92_30_10.bind2]
  rw [alnId_92 j hj]
  exact fastcode_of_div ⟨92, by decide⟩ _ _ _
    ((alnId_92 j hj) ▸ Q2.listedAt (⟨92, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨92, by decide⟩ : Fin 148) hj hq).1) colCertDiv_92_30_10_match


theorem leaf_92_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨92, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T92_30
      hfix92_30 hinj92_30 hcardT92_30
      (fun i => conj_mem_of_fixedPoints _ _ (T92_30 i) (hfix92_30 i) _)
      ⟨92, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T92_30_2 Q2.hfix92_30_2 Q2.hinj92_30_2
      Q2.hcardT92_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_30_2 i) (Q2.hfix92_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨92, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T92_30 = colFn colCertDiv_92_30_15.D1 (m := 25) from colCertDiv_92_30_15.bind1,
    show colData2 (⟨92, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 15 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T92_30_2 = colFn colCertDiv_92_30_15.D2 (m := 25) from colCertDiv_92_30_15.bind2]
  rw [alnId_92 j hj]
  exact fastcode_of_div ⟨92, by decide⟩ _ _ _
    ((alnId_92 j hj) ▸ Q2.listedAt (⟨92, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨92, by decide⟩ : Fin 148) hj hq).1) colCertDiv_92_30_15_match


theorem leaf_92_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨92, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T92_30
      hfix92_30 hinj92_30 hcardT92_30
      (fun i => conj_mem_of_fixedPoints _ _ (T92_30 i) (hfix92_30 i) _)
      ⟨92, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T92_30_2 Q2.hfix92_30_2 Q2.hinj92_30_2
      Q2.hcardT92_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_30_2 i) (Q2.hfix92_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨92, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T92_30 = colFn colCertDiv_92_30_20.D1 (m := 25) from colCertDiv_92_30_20.bind1,
    show colData2 (⟨92, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 20 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T92_30_2 = colFn colCertDiv_92_30_20.D2 (m := 25) from colCertDiv_92_30_20.bind2]
  rw [alnId_92 j hj]
  exact fastcode_of_div ⟨92, by decide⟩ _ _ _
    ((alnId_92 j hj) ▸ Q2.listedAt (⟨92, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨92, by decide⟩ : Fin 148) hj hq).1) colCertDiv_92_30_20_match


theorem leaf_92_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T92_53
      hfix92_53 hinj92_53 hcardT92_53
      (fun i => conj_mem_of_fixedPoints _ _ (T92_53 i) (hfix92_53 i) _)
      ⟨92, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T92_53_2 Q2.hfix92_53_2 Q2.hinj92_53_2
      Q2.hcardT92_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_53_2 i) (Q2.hfix92_53_2 i) _)
      colCert_92_53_0.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T92_53
      hfix92_53 hinj92_53 hcardT92_53
      (fun i => conj_mem_of_fixedPoints _ _ (T92_53 i) (hfix92_53 i) _)
      ⟨92, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T92_53_2 Q2.hfix92_53_2 Q2.hinj92_53_2
      Q2.hcardT92_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_53_2 i) (Q2.hfix92_53_2 i) _)
      colCert_92_53_1.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T92_53
      hfix92_53 hinj92_53 hcardT92_53
      (fun i => conj_mem_of_fixedPoints _ _ (T92_53 i) (hfix92_53 i) _)
      ⟨92, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T92_53_2 Q2.hfix92_53_2 Q2.hinj92_53_2
      Q2.hcardT92_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_53_2 i) (Q2.hfix92_53_2 i) _)
      colCert_92_53_2.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T92_53
      hfix92_53 hinj92_53 hcardT92_53
      (fun i => conj_mem_of_fixedPoints _ _ (T92_53 i) (hfix92_53 i) _)
      ⟨92, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T92_53_2 Q2.hfix92_53_2 Q2.hinj92_53_2
      Q2.hcardT92_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_53_2 i) (Q2.hfix92_53_2 i) _)
      colCert_92_53_3.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T92_53
      hfix92_53 hinj92_53 hcardT92_53
      (fun i => conj_mem_of_fixedPoints _ _ (T92_53 i) (hfix92_53 i) _)
      ⟨92, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T92_53_2 Q2.hfix92_53_2 Q2.hinj92_53_2
      Q2.hcardT92_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_53_2 i) (Q2.hfix92_53_2 i) _)
      colCert_92_53_4.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T92_53
      hfix92_53 hinj92_53 hcardT92_53
      (fun i => conj_mem_of_fixedPoints _ _ (T92_53 i) (hfix92_53 i) _)
      ⟨92, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T92_53_2 Q2.hfix92_53_2 Q2.hinj92_53_2
      Q2.hcardT92_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_53_2 i) (Q2.hfix92_53_2 i) _)
      colCert_92_53_5.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T92_53
      hfix92_53 hinj92_53 hcardT92_53
      (fun i => conj_mem_of_fixedPoints _ _ (T92_53 i) (hfix92_53 i) _)
      ⟨92, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T92_53_2 Q2.hfix92_53_2 Q2.hinj92_53_2
      Q2.hcardT92_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_53_2 i) (Q2.hfix92_53_2 i) _)
      colCert_92_53_10.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T92_53
      hfix92_53 hinj92_53 hcardT92_53
      (fun i => conj_mem_of_fixedPoints _ _ (T92_53 i) (hfix92_53 i) _)
      ⟨92, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T92_53_2 Q2.hfix92_53_2 Q2.hinj92_53_2
      Q2.hcardT92_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_53_2 i) (Q2.hfix92_53_2 i) _)
      colCert_92_53_15.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T92_53
      hfix92_53 hinj92_53 hcardT92_53
      (fun i => conj_mem_of_fixedPoints _ _ (T92_53 i) (hfix92_53 i) _)
      ⟨92, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T92_53_2 Q2.hfix92_53_2 Q2.hinj92_53_2
      Q2.hcardT92_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_53_2 i) (Q2.hfix92_53_2 i) _)
      colCert_92_53_20.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_92_0 (hp : 0 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 0 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp)) T92_92
      hfix92_92 hinj92_92 hcardT92_92
      (fun i => conj_mem_of_fixedPoints _ _ (T92_92 i) (hfix92_92 i) _)
      ⟨92, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 0 hp) Q2.T92_92_2 Q2.hfix92_92_2 Q2.hinj92_92_2
      Q2.hcardT92_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_92_2 i) (Q2.hfix92_92_2 i) _)
      colCert_92_92_0.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_92_1 (hp : 1 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 1 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp)) T92_92
      hfix92_92 hinj92_92 hcardT92_92
      (fun i => conj_mem_of_fixedPoints _ _ (T92_92 i) (hfix92_92 i) _)
      ⟨92, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 1 hp) Q2.T92_92_2 Q2.hfix92_92_2 Q2.hinj92_92_2
      Q2.hcardT92_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_92_2 i) (Q2.hfix92_92_2 i) _)
      colCert_92_92_1.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_92_2 (hp : 2 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 2 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp)) T92_92
      hfix92_92 hinj92_92 hcardT92_92
      (fun i => conj_mem_of_fixedPoints _ _ (T92_92 i) (hfix92_92 i) _)
      ⟨92, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 2 hp) Q2.T92_92_2 Q2.hfix92_92_2 Q2.hinj92_92_2
      Q2.hcardT92_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_92_2 i) (Q2.hfix92_92_2 i) _)
      colCert_92_92_2.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_92_3 (hp : 3 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 3 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp)) T92_92
      hfix92_92 hinj92_92 hcardT92_92
      (fun i => conj_mem_of_fixedPoints _ _ (T92_92 i) (hfix92_92 i) _)
      ⟨92, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 3 hp) Q2.T92_92_2 Q2.hfix92_92_2 Q2.hinj92_92_2
      Q2.hcardT92_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_92_2 i) (Q2.hfix92_92_2 i) _)
      colCert_92_92_3.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_92_4 (hp : 4 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 4 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp)) T92_92
      hfix92_92 hinj92_92 hcardT92_92
      (fun i => conj_mem_of_fixedPoints _ _ (T92_92 i) (hfix92_92 i) _)
      ⟨92, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 4 hp) Q2.T92_92_2 Q2.hfix92_92_2 Q2.hinj92_92_2
      Q2.hcardT92_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_92_2 i) (Q2.hfix92_92_2 i) _)
      colCert_92_92_4.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_92_5 (hp : 5 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 5 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp)) T92_92
      hfix92_92 hinj92_92 hcardT92_92
      (fun i => conj_mem_of_fixedPoints _ _ (T92_92 i) (hfix92_92 i) _)
      ⟨92, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 5 hp) Q2.T92_92_2 Q2.hfix92_92_2 Q2.hinj92_92_2
      Q2.hcardT92_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_92_2 i) (Q2.hfix92_92_2 i) _)
      colCert_92_92_5.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_92_10 (hp : 10 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 10 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp)) T92_92
      hfix92_92 hinj92_92 hcardT92_92
      (fun i => conj_mem_of_fixedPoints _ _ (T92_92 i) (hfix92_92 i) _)
      ⟨92, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 10 hp) Q2.T92_92_2 Q2.hfix92_92_2 Q2.hinj92_92_2
      Q2.hcardT92_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_92_2 i) (Q2.hfix92_92_2 i) _)
      colCert_92_92_10.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_92_15 (hp : 15 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 15 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp)) T92_92
      hfix92_92 hinj92_92 hcardT92_92
      (fun i => conj_mem_of_fixedPoints _ _ (T92_92 i) (hfix92_92 i) _)
      ⟨92, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 15 hp) Q2.T92_92_2 Q2.hfix92_92_2 Q2.hinj92_92_2
      Q2.hcardT92_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_92_2 i) (Q2.hfix92_92_2 i) _)
      colCert_92_92_15.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_92_92_20 (hp : 20 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 92 []).length)
    (hq : (normIsRep.getD 92 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 20 hp)
        (rowE2 (⟨92, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp))
        (rowE1 (⟨92, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨92, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨92, by decide⟩ (listedAt ⟨92, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp)) T92_92
      hfix92_92 hinj92_92 hcardT92_92
      (fun i => conj_mem_of_fixedPoints _ _ (T92_92 i) (hfix92_92 i) _)
      ⟨92, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨92, by decide⟩ (Q2.listedAt ⟨92, by decide⟩
        (alnCheck_rep ⟨92, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 20 hp) Q2.T92_92_2 Q2.hfix92_92_2 Q2.hinj92_92_2
      Q2.hcardT92_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T92_92_2 i) (Q2.hfix92_92_2 i) _)
      colCert_92_92_20.hD ?_).symm
  rw [alnId_92 j hj]


theorem leaf_93_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T93_10
      hfix93_10 hinj93_10 hcardT93_10
      (fun i => conj_mem_of_fixedPoints _ _ (T93_10 i) (hfix93_10 i) _)
      ⟨93, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T93_10_2 Q2.hfix93_10_2 Q2.hinj93_10_2
      Q2.hcardT93_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_10_2 i) (Q2.hfix93_10_2 i) _)
      colCert_93_10_0.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T93_10
      hfix93_10 hinj93_10 hcardT93_10
      (fun i => conj_mem_of_fixedPoints _ _ (T93_10 i) (hfix93_10 i) _)
      ⟨93, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T93_10_2 Q2.hfix93_10_2 Q2.hinj93_10_2
      Q2.hcardT93_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_10_2 i) (Q2.hfix93_10_2 i) _)
      colCert_93_10_1.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T93_10
      hfix93_10 hinj93_10 hcardT93_10
      (fun i => conj_mem_of_fixedPoints _ _ (T93_10 i) (hfix93_10 i) _)
      ⟨93, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T93_10_2 Q2.hfix93_10_2 Q2.hinj93_10_2
      Q2.hcardT93_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_10_2 i) (Q2.hfix93_10_2 i) _)
      colCert_93_10_2.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T93_10
      hfix93_10 hinj93_10 hcardT93_10
      (fun i => conj_mem_of_fixedPoints _ _ (T93_10 i) (hfix93_10 i) _)
      ⟨93, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T93_10_2 Q2.hfix93_10_2 Q2.hinj93_10_2
      Q2.hcardT93_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_10_2 i) (Q2.hfix93_10_2 i) _)
      colCert_93_10_3.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T93_10
      hfix93_10 hinj93_10 hcardT93_10
      (fun i => conj_mem_of_fixedPoints _ _ (T93_10 i) (hfix93_10 i) _)
      ⟨93, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T93_10_2 Q2.hfix93_10_2 Q2.hinj93_10_2
      Q2.hcardT93_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_10_2 i) (Q2.hfix93_10_2 i) _)
      colCert_93_10_4.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T93_12
      hfix93_12 hinj93_12 hcardT93_12
      (fun i => conj_mem_of_fixedPoints _ _ (T93_12 i) (hfix93_12 i) _)
      ⟨93, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T93_12_2 Q2.hfix93_12_2 Q2.hinj93_12_2
      Q2.hcardT93_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_12_2 i) (Q2.hfix93_12_2 i) _)
      colCert_93_12_0.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T93_12
      hfix93_12 hinj93_12 hcardT93_12
      (fun i => conj_mem_of_fixedPoints _ _ (T93_12 i) (hfix93_12 i) _)
      ⟨93, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T93_12_2 Q2.hfix93_12_2 Q2.hinj93_12_2
      Q2.hcardT93_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_12_2 i) (Q2.hfix93_12_2 i) _)
      colCert_93_12_1.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T93_12
      hfix93_12 hinj93_12 hcardT93_12
      (fun i => conj_mem_of_fixedPoints _ _ (T93_12 i) (hfix93_12 i) _)
      ⟨93, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T93_12_2 Q2.hfix93_12_2 Q2.hinj93_12_2
      Q2.hcardT93_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_12_2 i) (Q2.hfix93_12_2 i) _)
      colCert_93_12_2.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T93_12
      hfix93_12 hinj93_12 hcardT93_12
      (fun i => conj_mem_of_fixedPoints _ _ (T93_12 i) (hfix93_12 i) _)
      ⟨93, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T93_12_2 Q2.hfix93_12_2 Q2.hinj93_12_2
      Q2.hcardT93_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_12_2 i) (Q2.hfix93_12_2 i) _)
      colCert_93_12_3.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T93_12
      hfix93_12 hinj93_12 hcardT93_12
      (fun i => conj_mem_of_fixedPoints _ _ (T93_12 i) (hfix93_12 i) _)
      ⟨93, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T93_12_2 Q2.hfix93_12_2 Q2.hinj93_12_2
      Q2.hcardT93_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_12_2 i) (Q2.hfix93_12_2 i) _)
      colCert_93_12_4.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T93_31
      hfix93_31 hinj93_31 hcardT93_31
      (fun i => conj_mem_of_fixedPoints _ _ (T93_31 i) (hfix93_31 i) _)
      ⟨93, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T93_31_2 Q2.hfix93_31_2 Q2.hinj93_31_2
      Q2.hcardT93_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_31_2 i) (Q2.hfix93_31_2 i) _)
      colCert_93_31_0.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T93_31
      hfix93_31 hinj93_31 hcardT93_31
      (fun i => conj_mem_of_fixedPoints _ _ (T93_31 i) (hfix93_31 i) _)
      ⟨93, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T93_31_2 Q2.hfix93_31_2 Q2.hinj93_31_2
      Q2.hcardT93_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_31_2 i) (Q2.hfix93_31_2 i) _)
      colCert_93_31_1.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T93_31
      hfix93_31 hinj93_31 hcardT93_31
      (fun i => conj_mem_of_fixedPoints _ _ (T93_31 i) (hfix93_31 i) _)
      ⟨93, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T93_31_2 Q2.hfix93_31_2 Q2.hinj93_31_2
      Q2.hcardT93_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_31_2 i) (Q2.hfix93_31_2 i) _)
      colCert_93_31_2.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T93_31
      hfix93_31 hinj93_31 hcardT93_31
      (fun i => conj_mem_of_fixedPoints _ _ (T93_31 i) (hfix93_31 i) _)
      ⟨93, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T93_31_2 Q2.hfix93_31_2 Q2.hinj93_31_2
      Q2.hcardT93_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_31_2 i) (Q2.hfix93_31_2 i) _)
      colCert_93_31_3.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T93_31
      hfix93_31 hinj93_31 hcardT93_31
      (fun i => conj_mem_of_fixedPoints _ _ (T93_31 i) (hfix93_31 i) _)
      ⟨93, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T93_31_2 Q2.hfix93_31_2 Q2.hinj93_31_2
      Q2.hcardT93_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_31_2 i) (Q2.hfix93_31_2 i) _)
      colCert_93_31_4.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨93, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T93_31
      hfix93_31 hinj93_31 hcardT93_31
      (fun i => conj_mem_of_fixedPoints _ _ (T93_31 i) (hfix93_31 i) _)
      ⟨93, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T93_31_2 Q2.hfix93_31_2 Q2.hinj93_31_2
      Q2.hcardT93_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_31_2 i) (Q2.hfix93_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨93, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T93_31 = colFn colCertDiv_93_31_5.D1 (m := 25) from colCertDiv_93_31_5.bind1,
    show colData2 (⟨93, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 5 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T93_31_2 = colFn colCertDiv_93_31_5.D2 (m := 25) from colCertDiv_93_31_5.bind2]
  rw [alnId_93 j hj]
  exact fastcode_of_div ⟨93, by decide⟩ _ _ _
    ((alnId_93 j hj) ▸ Q2.listedAt (⟨93, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨93, by decide⟩ : Fin 148) hj hq).1) colCertDiv_93_31_5_match


theorem leaf_93_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨93, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T93_31
      hfix93_31 hinj93_31 hcardT93_31
      (fun i => conj_mem_of_fixedPoints _ _ (T93_31 i) (hfix93_31 i) _)
      ⟨93, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T93_31_2 Q2.hfix93_31_2 Q2.hinj93_31_2
      Q2.hcardT93_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_31_2 i) (Q2.hfix93_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨93, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T93_31 = colFn colCertDiv_93_31_10.D1 (m := 25) from colCertDiv_93_31_10.bind1,
    show colData2 (⟨93, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 10 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T93_31_2 = colFn colCertDiv_93_31_10.D2 (m := 25) from colCertDiv_93_31_10.bind2]
  rw [alnId_93 j hj]
  exact fastcode_of_div ⟨93, by decide⟩ _ _ _
    ((alnId_93 j hj) ▸ Q2.listedAt (⟨93, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨93, by decide⟩ : Fin 148) hj hq).1) colCertDiv_93_31_10_match


theorem leaf_93_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨93, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T93_31
      hfix93_31 hinj93_31 hcardT93_31
      (fun i => conj_mem_of_fixedPoints _ _ (T93_31 i) (hfix93_31 i) _)
      ⟨93, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T93_31_2 Q2.hfix93_31_2 Q2.hinj93_31_2
      Q2.hcardT93_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_31_2 i) (Q2.hfix93_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨93, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T93_31 = colFn colCertDiv_93_31_15.D1 (m := 25) from colCertDiv_93_31_15.bind1,
    show colData2 (⟨93, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 15 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T93_31_2 = colFn colCertDiv_93_31_15.D2 (m := 25) from colCertDiv_93_31_15.bind2]
  rw [alnId_93 j hj]
  exact fastcode_of_div ⟨93, by decide⟩ _ _ _
    ((alnId_93 j hj) ▸ Q2.listedAt (⟨93, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨93, by decide⟩ : Fin 148) hj hq).1) colCertDiv_93_31_15_match


theorem leaf_93_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨93, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T93_31
      hfix93_31 hinj93_31 hcardT93_31
      (fun i => conj_mem_of_fixedPoints _ _ (T93_31 i) (hfix93_31 i) _)
      ⟨93, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T93_31_2 Q2.hfix93_31_2 Q2.hinj93_31_2
      Q2.hcardT93_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_31_2 i) (Q2.hfix93_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨93, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T93_31 = colFn colCertDiv_93_31_20.D1 (m := 25) from colCertDiv_93_31_20.bind1,
    show colData2 (⟨93, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 20 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T93_31_2 = colFn colCertDiv_93_31_20.D2 (m := 25) from colCertDiv_93_31_20.bind2]
  rw [alnId_93 j hj]
  exact fastcode_of_div ⟨93, by decide⟩ _ _ _
    ((alnId_93 j hj) ▸ Q2.listedAt (⟨93, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨93, by decide⟩ : Fin 148) hj hq).1) colCertDiv_93_31_20_match


theorem leaf_93_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T93_53
      hfix93_53 hinj93_53 hcardT93_53
      (fun i => conj_mem_of_fixedPoints _ _ (T93_53 i) (hfix93_53 i) _)
      ⟨93, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T93_53_2 Q2.hfix93_53_2 Q2.hinj93_53_2
      Q2.hcardT93_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_53_2 i) (Q2.hfix93_53_2 i) _)
      colCert_93_53_0.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T93_53
      hfix93_53 hinj93_53 hcardT93_53
      (fun i => conj_mem_of_fixedPoints _ _ (T93_53 i) (hfix93_53 i) _)
      ⟨93, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T93_53_2 Q2.hfix93_53_2 Q2.hinj93_53_2
      Q2.hcardT93_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_53_2 i) (Q2.hfix93_53_2 i) _)
      colCert_93_53_1.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T93_53
      hfix93_53 hinj93_53 hcardT93_53
      (fun i => conj_mem_of_fixedPoints _ _ (T93_53 i) (hfix93_53 i) _)
      ⟨93, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T93_53_2 Q2.hfix93_53_2 Q2.hinj93_53_2
      Q2.hcardT93_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_53_2 i) (Q2.hfix93_53_2 i) _)
      colCert_93_53_2.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T93_53
      hfix93_53 hinj93_53 hcardT93_53
      (fun i => conj_mem_of_fixedPoints _ _ (T93_53 i) (hfix93_53 i) _)
      ⟨93, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T93_53_2 Q2.hfix93_53_2 Q2.hinj93_53_2
      Q2.hcardT93_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_53_2 i) (Q2.hfix93_53_2 i) _)
      colCert_93_53_3.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T93_53
      hfix93_53 hinj93_53 hcardT93_53
      (fun i => conj_mem_of_fixedPoints _ _ (T93_53 i) (hfix93_53 i) _)
      ⟨93, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T93_53_2 Q2.hfix93_53_2 Q2.hinj93_53_2
      Q2.hcardT93_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_53_2 i) (Q2.hfix93_53_2 i) _)
      colCert_93_53_4.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T93_53
      hfix93_53 hinj93_53 hcardT93_53
      (fun i => conj_mem_of_fixedPoints _ _ (T93_53 i) (hfix93_53 i) _)
      ⟨93, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T93_53_2 Q2.hfix93_53_2 Q2.hinj93_53_2
      Q2.hcardT93_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_53_2 i) (Q2.hfix93_53_2 i) _)
      colCert_93_53_5.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T93_53
      hfix93_53 hinj93_53 hcardT93_53
      (fun i => conj_mem_of_fixedPoints _ _ (T93_53 i) (hfix93_53 i) _)
      ⟨93, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T93_53_2 Q2.hfix93_53_2 Q2.hinj93_53_2
      Q2.hcardT93_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_53_2 i) (Q2.hfix93_53_2 i) _)
      colCert_93_53_10.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T93_53
      hfix93_53 hinj93_53 hcardT93_53
      (fun i => conj_mem_of_fixedPoints _ _ (T93_53 i) (hfix93_53 i) _)
      ⟨93, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T93_53_2 Q2.hfix93_53_2 Q2.hinj93_53_2
      Q2.hcardT93_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_53_2 i) (Q2.hfix93_53_2 i) _)
      colCert_93_53_15.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T93_53
      hfix93_53 hinj93_53 hcardT93_53
      (fun i => conj_mem_of_fixedPoints _ _ (T93_53 i) (hfix93_53 i) _)
      ⟨93, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T93_53_2 Q2.hfix93_53_2 Q2.hinj93_53_2
      Q2.hcardT93_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_53_2 i) (Q2.hfix93_53_2 i) _)
      colCert_93_53_20.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_93_0 (hp : 0 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 0 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp)) T93_93
      hfix93_93 hinj93_93 hcardT93_93
      (fun i => conj_mem_of_fixedPoints _ _ (T93_93 i) (hfix93_93 i) _)
      ⟨93, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 0 hp) Q2.T93_93_2 Q2.hfix93_93_2 Q2.hinj93_93_2
      Q2.hcardT93_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_93_2 i) (Q2.hfix93_93_2 i) _)
      colCert_93_93_0.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_93_1 (hp : 1 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 1 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp)) T93_93
      hfix93_93 hinj93_93 hcardT93_93
      (fun i => conj_mem_of_fixedPoints _ _ (T93_93 i) (hfix93_93 i) _)
      ⟨93, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 1 hp) Q2.T93_93_2 Q2.hfix93_93_2 Q2.hinj93_93_2
      Q2.hcardT93_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_93_2 i) (Q2.hfix93_93_2 i) _)
      colCert_93_93_1.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_93_2 (hp : 2 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 2 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp)) T93_93
      hfix93_93 hinj93_93 hcardT93_93
      (fun i => conj_mem_of_fixedPoints _ _ (T93_93 i) (hfix93_93 i) _)
      ⟨93, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 2 hp) Q2.T93_93_2 Q2.hfix93_93_2 Q2.hinj93_93_2
      Q2.hcardT93_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_93_2 i) (Q2.hfix93_93_2 i) _)
      colCert_93_93_2.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_93_3 (hp : 3 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 3 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp)) T93_93
      hfix93_93 hinj93_93 hcardT93_93
      (fun i => conj_mem_of_fixedPoints _ _ (T93_93 i) (hfix93_93 i) _)
      ⟨93, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 3 hp) Q2.T93_93_2 Q2.hfix93_93_2 Q2.hinj93_93_2
      Q2.hcardT93_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_93_2 i) (Q2.hfix93_93_2 i) _)
      colCert_93_93_3.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_93_4 (hp : 4 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 4 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp)) T93_93
      hfix93_93 hinj93_93 hcardT93_93
      (fun i => conj_mem_of_fixedPoints _ _ (T93_93 i) (hfix93_93 i) _)
      ⟨93, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 4 hp) Q2.T93_93_2 Q2.hfix93_93_2 Q2.hinj93_93_2
      Q2.hcardT93_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_93_2 i) (Q2.hfix93_93_2 i) _)
      colCert_93_93_4.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_93_5 (hp : 5 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 5 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp)) T93_93
      hfix93_93 hinj93_93 hcardT93_93
      (fun i => conj_mem_of_fixedPoints _ _ (T93_93 i) (hfix93_93 i) _)
      ⟨93, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 5 hp) Q2.T93_93_2 Q2.hfix93_93_2 Q2.hinj93_93_2
      Q2.hcardT93_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_93_2 i) (Q2.hfix93_93_2 i) _)
      colCert_93_93_5.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_93_10 (hp : 10 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 10 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp)) T93_93
      hfix93_93 hinj93_93 hcardT93_93
      (fun i => conj_mem_of_fixedPoints _ _ (T93_93 i) (hfix93_93 i) _)
      ⟨93, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 10 hp) Q2.T93_93_2 Q2.hfix93_93_2 Q2.hinj93_93_2
      Q2.hcardT93_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_93_2 i) (Q2.hfix93_93_2 i) _)
      colCert_93_93_10.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_93_15 (hp : 15 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 15 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp)) T93_93
      hfix93_93 hinj93_93 hcardT93_93
      (fun i => conj_mem_of_fixedPoints _ _ (T93_93 i) (hfix93_93 i) _)
      ⟨93, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 15 hp) Q2.T93_93_2 Q2.hfix93_93_2 Q2.hinj93_93_2
      Q2.hcardT93_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_93_2 i) (Q2.hfix93_93_2 i) _)
      colCert_93_93_15.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_93_93_20 (hp : 20 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 93 []).length)
    (hq : (normIsRep.getD 93 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 20 hp)
        (rowE2 (⟨93, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp))
        (rowE1 (⟨93, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨93, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨93, by decide⟩ (listedAt ⟨93, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp)) T93_93
      hfix93_93 hinj93_93 hcardT93_93
      (fun i => conj_mem_of_fixedPoints _ _ (T93_93 i) (hfix93_93 i) _)
      ⟨93, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨93, by decide⟩ (Q2.listedAt ⟨93, by decide⟩
        (alnCheck_rep ⟨93, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 20 hp) Q2.T93_93_2 Q2.hfix93_93_2 Q2.hinj93_93_2
      Q2.hcardT93_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T93_93_2 i) (Q2.hfix93_93_2 i) _)
      colCert_93_93_20.hD ?_).symm
  rw [alnId_93 j hj]


theorem leaf_94_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T94_10
      hfix94_10 hinj94_10 hcardT94_10
      (fun i => conj_mem_of_fixedPoints _ _ (T94_10 i) (hfix94_10 i) _)
      ⟨94, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T94_10_2 Q2.hfix94_10_2 Q2.hinj94_10_2
      Q2.hcardT94_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_10_2 i) (Q2.hfix94_10_2 i) _)
      colCert_94_10_0.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T94_10
      hfix94_10 hinj94_10 hcardT94_10
      (fun i => conj_mem_of_fixedPoints _ _ (T94_10 i) (hfix94_10 i) _)
      ⟨94, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T94_10_2 Q2.hfix94_10_2 Q2.hinj94_10_2
      Q2.hcardT94_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_10_2 i) (Q2.hfix94_10_2 i) _)
      colCert_94_10_1.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T94_10
      hfix94_10 hinj94_10 hcardT94_10
      (fun i => conj_mem_of_fixedPoints _ _ (T94_10 i) (hfix94_10 i) _)
      ⟨94, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T94_10_2 Q2.hfix94_10_2 Q2.hinj94_10_2
      Q2.hcardT94_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_10_2 i) (Q2.hfix94_10_2 i) _)
      colCert_94_10_2.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T94_10
      hfix94_10 hinj94_10 hcardT94_10
      (fun i => conj_mem_of_fixedPoints _ _ (T94_10 i) (hfix94_10 i) _)
      ⟨94, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T94_10_2 Q2.hfix94_10_2 Q2.hinj94_10_2
      Q2.hcardT94_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_10_2 i) (Q2.hfix94_10_2 i) _)
      colCert_94_10_3.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T94_10
      hfix94_10 hinj94_10 hcardT94_10
      (fun i => conj_mem_of_fixedPoints _ _ (T94_10 i) (hfix94_10 i) _)
      ⟨94, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T94_10_2 Q2.hfix94_10_2 Q2.hinj94_10_2
      Q2.hcardT94_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_10_2 i) (Q2.hfix94_10_2 i) _)
      colCert_94_10_4.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T94_12
      hfix94_12 hinj94_12 hcardT94_12
      (fun i => conj_mem_of_fixedPoints _ _ (T94_12 i) (hfix94_12 i) _)
      ⟨94, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T94_12_2 Q2.hfix94_12_2 Q2.hinj94_12_2
      Q2.hcardT94_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_12_2 i) (Q2.hfix94_12_2 i) _)
      colCert_94_12_0.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T94_12
      hfix94_12 hinj94_12 hcardT94_12
      (fun i => conj_mem_of_fixedPoints _ _ (T94_12 i) (hfix94_12 i) _)
      ⟨94, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T94_12_2 Q2.hfix94_12_2 Q2.hinj94_12_2
      Q2.hcardT94_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_12_2 i) (Q2.hfix94_12_2 i) _)
      colCert_94_12_1.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T94_12
      hfix94_12 hinj94_12 hcardT94_12
      (fun i => conj_mem_of_fixedPoints _ _ (T94_12 i) (hfix94_12 i) _)
      ⟨94, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T94_12_2 Q2.hfix94_12_2 Q2.hinj94_12_2
      Q2.hcardT94_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_12_2 i) (Q2.hfix94_12_2 i) _)
      colCert_94_12_2.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T94_12
      hfix94_12 hinj94_12 hcardT94_12
      (fun i => conj_mem_of_fixedPoints _ _ (T94_12 i) (hfix94_12 i) _)
      ⟨94, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T94_12_2 Q2.hfix94_12_2 Q2.hinj94_12_2
      Q2.hcardT94_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_12_2 i) (Q2.hfix94_12_2 i) _)
      colCert_94_12_3.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T94_12
      hfix94_12 hinj94_12 hcardT94_12
      (fun i => conj_mem_of_fixedPoints _ _ (T94_12 i) (hfix94_12 i) _)
      ⟨94, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T94_12_2 Q2.hfix94_12_2 Q2.hinj94_12_2
      Q2.hcardT94_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_12_2 i) (Q2.hfix94_12_2 i) _)
      colCert_94_12_4.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T94_32
      hfix94_32 hinj94_32 hcardT94_32
      (fun i => conj_mem_of_fixedPoints _ _ (T94_32 i) (hfix94_32 i) _)
      ⟨94, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T94_32_2 Q2.hfix94_32_2 Q2.hinj94_32_2
      Q2.hcardT94_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_32_2 i) (Q2.hfix94_32_2 i) _)
      colCert_94_32_0.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T94_32
      hfix94_32 hinj94_32 hcardT94_32
      (fun i => conj_mem_of_fixedPoints _ _ (T94_32 i) (hfix94_32 i) _)
      ⟨94, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T94_32_2 Q2.hfix94_32_2 Q2.hinj94_32_2
      Q2.hcardT94_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_32_2 i) (Q2.hfix94_32_2 i) _)
      colCert_94_32_1.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T94_32
      hfix94_32 hinj94_32 hcardT94_32
      (fun i => conj_mem_of_fixedPoints _ _ (T94_32 i) (hfix94_32 i) _)
      ⟨94, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T94_32_2 Q2.hfix94_32_2 Q2.hinj94_32_2
      Q2.hcardT94_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_32_2 i) (Q2.hfix94_32_2 i) _)
      colCert_94_32_2.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T94_32
      hfix94_32 hinj94_32 hcardT94_32
      (fun i => conj_mem_of_fixedPoints _ _ (T94_32 i) (hfix94_32 i) _)
      ⟨94, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T94_32_2 Q2.hfix94_32_2 Q2.hinj94_32_2
      Q2.hcardT94_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_32_2 i) (Q2.hfix94_32_2 i) _)
      colCert_94_32_3.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T94_32
      hfix94_32 hinj94_32 hcardT94_32
      (fun i => conj_mem_of_fixedPoints _ _ (T94_32 i) (hfix94_32 i) _)
      ⟨94, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T94_32_2 Q2.hfix94_32_2 Q2.hinj94_32_2
      Q2.hcardT94_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_32_2 i) (Q2.hfix94_32_2 i) _)
      colCert_94_32_4.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨94, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T94_32
      hfix94_32 hinj94_32 hcardT94_32
      (fun i => conj_mem_of_fixedPoints _ _ (T94_32 i) (hfix94_32 i) _)
      ⟨94, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T94_32_2 Q2.hfix94_32_2 Q2.hinj94_32_2
      Q2.hcardT94_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_32_2 i) (Q2.hfix94_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨94, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T94_32 = colFn colCertDiv_94_32_5.D1 (m := 25) from colCertDiv_94_32_5.bind1,
    show colData2 (⟨94, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 5 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T94_32_2 = colFn colCertDiv_94_32_5.D2 (m := 25) from colCertDiv_94_32_5.bind2]
  rw [alnId_94 j hj]
  exact fastcode_of_div ⟨94, by decide⟩ _ _ _
    ((alnId_94 j hj) ▸ Q2.listedAt (⟨94, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨94, by decide⟩ : Fin 148) hj hq).1) colCertDiv_94_32_5_match


theorem leaf_94_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨94, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T94_32
      hfix94_32 hinj94_32 hcardT94_32
      (fun i => conj_mem_of_fixedPoints _ _ (T94_32 i) (hfix94_32 i) _)
      ⟨94, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T94_32_2 Q2.hfix94_32_2 Q2.hinj94_32_2
      Q2.hcardT94_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_32_2 i) (Q2.hfix94_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨94, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T94_32 = colFn colCertDiv_94_32_10.D1 (m := 25) from colCertDiv_94_32_10.bind1,
    show colData2 (⟨94, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 10 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T94_32_2 = colFn colCertDiv_94_32_10.D2 (m := 25) from colCertDiv_94_32_10.bind2]
  rw [alnId_94 j hj]
  exact fastcode_of_div ⟨94, by decide⟩ _ _ _
    ((alnId_94 j hj) ▸ Q2.listedAt (⟨94, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨94, by decide⟩ : Fin 148) hj hq).1) colCertDiv_94_32_10_match


theorem leaf_94_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨94, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T94_32
      hfix94_32 hinj94_32 hcardT94_32
      (fun i => conj_mem_of_fixedPoints _ _ (T94_32 i) (hfix94_32 i) _)
      ⟨94, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T94_32_2 Q2.hfix94_32_2 Q2.hinj94_32_2
      Q2.hcardT94_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_32_2 i) (Q2.hfix94_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨94, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T94_32 = colFn colCertDiv_94_32_15.D1 (m := 25) from colCertDiv_94_32_15.bind1,
    show colData2 (⟨94, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 15 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T94_32_2 = colFn colCertDiv_94_32_15.D2 (m := 25) from colCertDiv_94_32_15.bind2]
  rw [alnId_94 j hj]
  exact fastcode_of_div ⟨94, by decide⟩ _ _ _
    ((alnId_94 j hj) ▸ Q2.listedAt (⟨94, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨94, by decide⟩ : Fin 148) hj hq).1) colCertDiv_94_32_15_match


theorem leaf_94_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨94, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T94_32
      hfix94_32 hinj94_32 hcardT94_32
      (fun i => conj_mem_of_fixedPoints _ _ (T94_32 i) (hfix94_32 i) _)
      ⟨94, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T94_32_2 Q2.hfix94_32_2 Q2.hinj94_32_2
      Q2.hcardT94_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_32_2 i) (Q2.hfix94_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨94, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T94_32 = colFn colCertDiv_94_32_20.D1 (m := 25) from colCertDiv_94_32_20.bind1,
    show colData2 (⟨94, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 20 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T94_32_2 = colFn colCertDiv_94_32_20.D2 (m := 25) from colCertDiv_94_32_20.bind2]
  rw [alnId_94 j hj]
  exact fastcode_of_div ⟨94, by decide⟩ _ _ _
    ((alnId_94 j hj) ▸ Q2.listedAt (⟨94, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨94, by decide⟩ : Fin 148) hj hq).1) colCertDiv_94_32_20_match


theorem leaf_94_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T94_53
      hfix94_53 hinj94_53 hcardT94_53
      (fun i => conj_mem_of_fixedPoints _ _ (T94_53 i) (hfix94_53 i) _)
      ⟨94, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T94_53_2 Q2.hfix94_53_2 Q2.hinj94_53_2
      Q2.hcardT94_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_53_2 i) (Q2.hfix94_53_2 i) _)
      colCert_94_53_0.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T94_53
      hfix94_53 hinj94_53 hcardT94_53
      (fun i => conj_mem_of_fixedPoints _ _ (T94_53 i) (hfix94_53 i) _)
      ⟨94, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T94_53_2 Q2.hfix94_53_2 Q2.hinj94_53_2
      Q2.hcardT94_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_53_2 i) (Q2.hfix94_53_2 i) _)
      colCert_94_53_1.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T94_53
      hfix94_53 hinj94_53 hcardT94_53
      (fun i => conj_mem_of_fixedPoints _ _ (T94_53 i) (hfix94_53 i) _)
      ⟨94, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T94_53_2 Q2.hfix94_53_2 Q2.hinj94_53_2
      Q2.hcardT94_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_53_2 i) (Q2.hfix94_53_2 i) _)
      colCert_94_53_2.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T94_53
      hfix94_53 hinj94_53 hcardT94_53
      (fun i => conj_mem_of_fixedPoints _ _ (T94_53 i) (hfix94_53 i) _)
      ⟨94, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T94_53_2 Q2.hfix94_53_2 Q2.hinj94_53_2
      Q2.hcardT94_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_53_2 i) (Q2.hfix94_53_2 i) _)
      colCert_94_53_3.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T94_53
      hfix94_53 hinj94_53 hcardT94_53
      (fun i => conj_mem_of_fixedPoints _ _ (T94_53 i) (hfix94_53 i) _)
      ⟨94, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T94_53_2 Q2.hfix94_53_2 Q2.hinj94_53_2
      Q2.hcardT94_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_53_2 i) (Q2.hfix94_53_2 i) _)
      colCert_94_53_4.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T94_53
      hfix94_53 hinj94_53 hcardT94_53
      (fun i => conj_mem_of_fixedPoints _ _ (T94_53 i) (hfix94_53 i) _)
      ⟨94, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T94_53_2 Q2.hfix94_53_2 Q2.hinj94_53_2
      Q2.hcardT94_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_53_2 i) (Q2.hfix94_53_2 i) _)
      colCert_94_53_5.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T94_53
      hfix94_53 hinj94_53 hcardT94_53
      (fun i => conj_mem_of_fixedPoints _ _ (T94_53 i) (hfix94_53 i) _)
      ⟨94, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T94_53_2 Q2.hfix94_53_2 Q2.hinj94_53_2
      Q2.hcardT94_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_53_2 i) (Q2.hfix94_53_2 i) _)
      colCert_94_53_10.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T94_53
      hfix94_53 hinj94_53 hcardT94_53
      (fun i => conj_mem_of_fixedPoints _ _ (T94_53 i) (hfix94_53 i) _)
      ⟨94, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T94_53_2 Q2.hfix94_53_2 Q2.hinj94_53_2
      Q2.hcardT94_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_53_2 i) (Q2.hfix94_53_2 i) _)
      colCert_94_53_15.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T94_53
      hfix94_53 hinj94_53 hcardT94_53
      (fun i => conj_mem_of_fixedPoints _ _ (T94_53 i) (hfix94_53 i) _)
      ⟨94, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T94_53_2 Q2.hfix94_53_2 Q2.hinj94_53_2
      Q2.hcardT94_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_53_2 i) (Q2.hfix94_53_2 i) _)
      colCert_94_53_20.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_94_0 (hp : 0 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 0 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp)) T94_94
      hfix94_94 hinj94_94 hcardT94_94
      (fun i => conj_mem_of_fixedPoints _ _ (T94_94 i) (hfix94_94 i) _)
      ⟨94, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 0 hp) Q2.T94_94_2 Q2.hfix94_94_2 Q2.hinj94_94_2
      Q2.hcardT94_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_94_2 i) (Q2.hfix94_94_2 i) _)
      colCert_94_94_0.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_94_1 (hp : 1 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 1 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp)) T94_94
      hfix94_94 hinj94_94 hcardT94_94
      (fun i => conj_mem_of_fixedPoints _ _ (T94_94 i) (hfix94_94 i) _)
      ⟨94, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 1 hp) Q2.T94_94_2 Q2.hfix94_94_2 Q2.hinj94_94_2
      Q2.hcardT94_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_94_2 i) (Q2.hfix94_94_2 i) _)
      colCert_94_94_1.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_94_2 (hp : 2 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 2 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp)) T94_94
      hfix94_94 hinj94_94 hcardT94_94
      (fun i => conj_mem_of_fixedPoints _ _ (T94_94 i) (hfix94_94 i) _)
      ⟨94, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 2 hp) Q2.T94_94_2 Q2.hfix94_94_2 Q2.hinj94_94_2
      Q2.hcardT94_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_94_2 i) (Q2.hfix94_94_2 i) _)
      colCert_94_94_2.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_94_3 (hp : 3 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 3 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp)) T94_94
      hfix94_94 hinj94_94 hcardT94_94
      (fun i => conj_mem_of_fixedPoints _ _ (T94_94 i) (hfix94_94 i) _)
      ⟨94, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 3 hp) Q2.T94_94_2 Q2.hfix94_94_2 Q2.hinj94_94_2
      Q2.hcardT94_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_94_2 i) (Q2.hfix94_94_2 i) _)
      colCert_94_94_3.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_94_4 (hp : 4 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 4 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp)) T94_94
      hfix94_94 hinj94_94 hcardT94_94
      (fun i => conj_mem_of_fixedPoints _ _ (T94_94 i) (hfix94_94 i) _)
      ⟨94, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 4 hp) Q2.T94_94_2 Q2.hfix94_94_2 Q2.hinj94_94_2
      Q2.hcardT94_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_94_2 i) (Q2.hfix94_94_2 i) _)
      colCert_94_94_4.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_94_5 (hp : 5 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 5 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp)) T94_94
      hfix94_94 hinj94_94 hcardT94_94
      (fun i => conj_mem_of_fixedPoints _ _ (T94_94 i) (hfix94_94 i) _)
      ⟨94, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 5 hp) Q2.T94_94_2 Q2.hfix94_94_2 Q2.hinj94_94_2
      Q2.hcardT94_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_94_2 i) (Q2.hfix94_94_2 i) _)
      colCert_94_94_5.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_94_10 (hp : 10 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 10 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp)) T94_94
      hfix94_94 hinj94_94 hcardT94_94
      (fun i => conj_mem_of_fixedPoints _ _ (T94_94 i) (hfix94_94 i) _)
      ⟨94, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 10 hp) Q2.T94_94_2 Q2.hfix94_94_2 Q2.hinj94_94_2
      Q2.hcardT94_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_94_2 i) (Q2.hfix94_94_2 i) _)
      colCert_94_94_10.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_94_15 (hp : 15 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 15 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp)) T94_94
      hfix94_94 hinj94_94 hcardT94_94
      (fun i => conj_mem_of_fixedPoints _ _ (T94_94 i) (hfix94_94 i) _)
      ⟨94, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 15 hp) Q2.T94_94_2 Q2.hfix94_94_2 Q2.hinj94_94_2
      Q2.hcardT94_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_94_2 i) (Q2.hfix94_94_2 i) _)
      colCert_94_94_15.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_94_94_20 (hp : 20 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 94 []).length)
    (hq : (normIsRep.getD 94 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 20 hp)
        (rowE2 (⟨94, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp))
        (rowE1 (⟨94, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨94, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨94, by decide⟩ (listedAt ⟨94, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp)) T94_94
      hfix94_94 hinj94_94 hcardT94_94
      (fun i => conj_mem_of_fixedPoints _ _ (T94_94 i) (hfix94_94 i) _)
      ⟨94, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨94, by decide⟩ (Q2.listedAt ⟨94, by decide⟩
        (alnCheck_rep ⟨94, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 20 hp) Q2.T94_94_2 Q2.hfix94_94_2 Q2.hinj94_94_2
      Q2.hcardT94_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T94_94_2 i) (Q2.hfix94_94_2 i) _)
      colCert_94_94_20.hD ?_).symm
  rw [alnId_94 j hj]


theorem leaf_95_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T95_10
      hfix95_10 hinj95_10 hcardT95_10
      (fun i => conj_mem_of_fixedPoints _ _ (T95_10 i) (hfix95_10 i) _)
      ⟨95, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T95_10_2 Q2.hfix95_10_2 Q2.hinj95_10_2
      Q2.hcardT95_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_10_2 i) (Q2.hfix95_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T95_10 = colFn colCert_95_10_0.D (m := 25) from colCert_95_10_0.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 0 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T95_10_2 = colFn colCert_95_10_0.D (m := 25) from colCert_95_10_0.bind2]
  exact alnAll_95_10_0 j hj hq

theorem leaf_95_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T95_10
      hfix95_10 hinj95_10 hcardT95_10
      (fun i => conj_mem_of_fixedPoints _ _ (T95_10 i) (hfix95_10 i) _)
      ⟨95, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T95_10_2 Q2.hfix95_10_2 Q2.hinj95_10_2
      Q2.hcardT95_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_10_2 i) (Q2.hfix95_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T95_10 = colFn colCert_95_10_1.D (m := 25) from colCert_95_10_1.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 1 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T95_10_2 = colFn colCert_95_10_1.D (m := 25) from colCert_95_10_1.bind2]
  exact alnAll_95_10_1 j hj hq

theorem leaf_95_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T95_10
      hfix95_10 hinj95_10 hcardT95_10
      (fun i => conj_mem_of_fixedPoints _ _ (T95_10 i) (hfix95_10 i) _)
      ⟨95, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T95_10_2 Q2.hfix95_10_2 Q2.hinj95_10_2
      Q2.hcardT95_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_10_2 i) (Q2.hfix95_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T95_10 = colFn colCert_95_10_2.D (m := 25) from colCert_95_10_2.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 2 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T95_10_2 = colFn colCert_95_10_2.D (m := 25) from colCert_95_10_2.bind2]
  exact alnAll_95_10_2 j hj hq

theorem leaf_95_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T95_10
      hfix95_10 hinj95_10 hcardT95_10
      (fun i => conj_mem_of_fixedPoints _ _ (T95_10 i) (hfix95_10 i) _)
      ⟨95, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T95_10_2 Q2.hfix95_10_2 Q2.hinj95_10_2
      Q2.hcardT95_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_10_2 i) (Q2.hfix95_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T95_10 = colFn colCert_95_10_3.D (m := 25) from colCert_95_10_3.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 3 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T95_10_2 = colFn colCert_95_10_3.D (m := 25) from colCert_95_10_3.bind2]
  exact alnAll_95_10_3 j hj hq

theorem leaf_95_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T95_10
      hfix95_10 hinj95_10 hcardT95_10
      (fun i => conj_mem_of_fixedPoints _ _ (T95_10 i) (hfix95_10 i) _)
      ⟨95, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T95_10_2 Q2.hfix95_10_2 Q2.hinj95_10_2
      Q2.hcardT95_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_10_2 i) (Q2.hfix95_10_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp) : ↥(reps ⟨10, by decide⟩)) : Coordinate 1)
        T95_10 = colFn colCert_95_10_4.D (m := 25) from colCert_95_10_4.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨10, by decide⟩ 4 hp : ↥(Q2.reps ⟨10, by decide⟩)) : Coordinate 2)
        Q2.T95_10_2 = colFn colCert_95_10_4.D (m := 25) from colCert_95_10_4.bind2]
  exact alnAll_95_10_4 j hj hq

theorem leaf_95_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T95_12
      hfix95_12 hinj95_12 hcardT95_12
      (fun i => conj_mem_of_fixedPoints _ _ (T95_12 i) (hfix95_12 i) _)
      ⟨95, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T95_12_2 Q2.hfix95_12_2 Q2.hinj95_12_2
      Q2.hcardT95_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_12_2 i) (Q2.hfix95_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T95_12 = colFn colCert_95_12_0.D (m := 25) from colCert_95_12_0.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T95_12_2 = colFn colCert_95_12_0.D (m := 25) from colCert_95_12_0.bind2]
  exact alnAll_95_12_0 j hj hq

theorem leaf_95_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T95_12
      hfix95_12 hinj95_12 hcardT95_12
      (fun i => conj_mem_of_fixedPoints _ _ (T95_12 i) (hfix95_12 i) _)
      ⟨95, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T95_12_2 Q2.hfix95_12_2 Q2.hinj95_12_2
      Q2.hcardT95_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_12_2 i) (Q2.hfix95_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T95_12 = colFn colCert_95_12_1.D (m := 25) from colCert_95_12_1.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T95_12_2 = colFn colCert_95_12_1.D (m := 25) from colCert_95_12_1.bind2]
  exact alnAll_95_12_1 j hj hq

theorem leaf_95_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T95_12
      hfix95_12 hinj95_12 hcardT95_12
      (fun i => conj_mem_of_fixedPoints _ _ (T95_12 i) (hfix95_12 i) _)
      ⟨95, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T95_12_2 Q2.hfix95_12_2 Q2.hinj95_12_2
      Q2.hcardT95_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_12_2 i) (Q2.hfix95_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T95_12 = colFn colCert_95_12_2.D (m := 25) from colCert_95_12_2.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T95_12_2 = colFn colCert_95_12_2.D (m := 25) from colCert_95_12_2.bind2]
  exact alnAll_95_12_2 j hj hq

theorem leaf_95_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T95_12
      hfix95_12 hinj95_12 hcardT95_12
      (fun i => conj_mem_of_fixedPoints _ _ (T95_12 i) (hfix95_12 i) _)
      ⟨95, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T95_12_2 Q2.hfix95_12_2 Q2.hinj95_12_2
      Q2.hcardT95_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_12_2 i) (Q2.hfix95_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T95_12 = colFn colCert_95_12_3.D (m := 25) from colCert_95_12_3.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T95_12_2 = colFn colCert_95_12_3.D (m := 25) from colCert_95_12_3.bind2]
  exact alnAll_95_12_3 j hj hq

theorem leaf_95_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T95_12
      hfix95_12 hinj95_12 hcardT95_12
      (fun i => conj_mem_of_fixedPoints _ _ (T95_12 i) (hfix95_12 i) _)
      ⟨95, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T95_12_2 Q2.hfix95_12_2 Q2.hinj95_12_2
      Q2.hcardT95_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_12_2 i) (Q2.hfix95_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T95_12 = colFn colCert_95_12_4.D (m := 25) from colCert_95_12_4.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T95_12_2 = colFn colCert_95_12_4.D (m := 25) from colCert_95_12_4.bind2]
  exact alnAll_95_12_4 j hj hq

theorem leaf_95_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T95_33
      hfix95_33 hinj95_33 hcardT95_33
      (fun i => conj_mem_of_fixedPoints _ _ (T95_33 i) (hfix95_33 i) _)
      ⟨95, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T95_33_2 Q2.hfix95_33_2 Q2.hinj95_33_2
      Q2.hcardT95_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_33_2 i) (Q2.hfix95_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T95_33 = colFn colCert_95_33_0.D (m := 25) from colCert_95_33_0.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 0 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T95_33_2 = colFn colCert_95_33_0.D (m := 25) from colCert_95_33_0.bind2]
  exact alnAll_95_33_0 j hj hq

theorem leaf_95_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T95_33
      hfix95_33 hinj95_33 hcardT95_33
      (fun i => conj_mem_of_fixedPoints _ _ (T95_33 i) (hfix95_33 i) _)
      ⟨95, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T95_33_2 Q2.hfix95_33_2 Q2.hinj95_33_2
      Q2.hcardT95_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_33_2 i) (Q2.hfix95_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T95_33 = colFn colCert_95_33_1.D (m := 25) from colCert_95_33_1.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 1 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T95_33_2 = colFn colCert_95_33_1.D (m := 25) from colCert_95_33_1.bind2]
  exact alnAll_95_33_1 j hj hq

theorem leaf_95_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T95_33
      hfix95_33 hinj95_33 hcardT95_33
      (fun i => conj_mem_of_fixedPoints _ _ (T95_33 i) (hfix95_33 i) _)
      ⟨95, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T95_33_2 Q2.hfix95_33_2 Q2.hinj95_33_2
      Q2.hcardT95_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_33_2 i) (Q2.hfix95_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T95_33 = colFn colCert_95_33_2.D (m := 25) from colCert_95_33_2.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 2 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T95_33_2 = colFn colCert_95_33_2.D (m := 25) from colCert_95_33_2.bind2]
  exact alnAll_95_33_2 j hj hq

theorem leaf_95_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T95_33
      hfix95_33 hinj95_33 hcardT95_33
      (fun i => conj_mem_of_fixedPoints _ _ (T95_33 i) (hfix95_33 i) _)
      ⟨95, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T95_33_2 Q2.hfix95_33_2 Q2.hinj95_33_2
      Q2.hcardT95_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_33_2 i) (Q2.hfix95_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T95_33 = colFn colCert_95_33_3.D (m := 25) from colCert_95_33_3.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 3 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T95_33_2 = colFn colCert_95_33_3.D (m := 25) from colCert_95_33_3.bind2]
  exact alnAll_95_33_3 j hj hq

theorem leaf_95_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T95_33
      hfix95_33 hinj95_33 hcardT95_33
      (fun i => conj_mem_of_fixedPoints _ _ (T95_33 i) (hfix95_33 i) _)
      ⟨95, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T95_33_2 Q2.hfix95_33_2 Q2.hinj95_33_2
      Q2.hcardT95_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_33_2 i) (Q2.hfix95_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T95_33 = colFn colCert_95_33_4.D (m := 25) from colCert_95_33_4.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 4 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T95_33_2 = colFn colCert_95_33_4.D (m := 25) from colCert_95_33_4.bind2]
  exact alnAll_95_33_4 j hj hq

theorem leaf_95_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T95_33
      hfix95_33 hinj95_33 hcardT95_33
      (fun i => conj_mem_of_fixedPoints _ _ (T95_33 i) (hfix95_33 i) _)
      ⟨95, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T95_33_2 Q2.hfix95_33_2 Q2.hinj95_33_2
      Q2.hcardT95_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_33_2 i) (Q2.hfix95_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T95_33 = colFn colCertDiv_95_33_5.D1 (m := 25) from colCertDiv_95_33_5.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T95_33_2 = colFn colCertDiv_95_33_5.D2 (m := 25) from colCertDiv_95_33_5.bind2]
  exact alnAll_95_33_5 j hj hq

theorem leaf_95_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T95_33
      hfix95_33 hinj95_33 hcardT95_33
      (fun i => conj_mem_of_fixedPoints _ _ (T95_33 i) (hfix95_33 i) _)
      ⟨95, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T95_33_2 Q2.hfix95_33_2 Q2.hinj95_33_2
      Q2.hcardT95_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_33_2 i) (Q2.hfix95_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T95_33 = colFn colCertDiv_95_33_10.D1 (m := 25) from colCertDiv_95_33_10.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T95_33_2 = colFn colCertDiv_95_33_10.D2 (m := 25) from colCertDiv_95_33_10.bind2]
  exact alnAll_95_33_10 j hj hq

theorem leaf_95_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T95_33
      hfix95_33 hinj95_33 hcardT95_33
      (fun i => conj_mem_of_fixedPoints _ _ (T95_33 i) (hfix95_33 i) _)
      ⟨95, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T95_33_2 Q2.hfix95_33_2 Q2.hinj95_33_2
      Q2.hcardT95_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_33_2 i) (Q2.hfix95_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T95_33 = colFn colCertDiv_95_33_15.D1 (m := 25) from colCertDiv_95_33_15.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T95_33_2 = colFn colCertDiv_95_33_15.D2 (m := 25) from colCertDiv_95_33_15.bind2]
  exact alnAll_95_33_15 j hj hq

theorem leaf_95_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T95_33
      hfix95_33 hinj95_33 hcardT95_33
      (fun i => conj_mem_of_fixedPoints _ _ (T95_33 i) (hfix95_33 i) _)
      ⟨95, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T95_33_2 Q2.hfix95_33_2 Q2.hinj95_33_2
      Q2.hcardT95_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_33_2 i) (Q2.hfix95_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T95_33 = colFn colCertDiv_95_33_20.D1 (m := 25) from colCertDiv_95_33_20.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T95_33_2 = colFn colCertDiv_95_33_20.D2 (m := 25) from colCertDiv_95_33_20.bind2]
  exact alnAll_95_33_20 j hj hq

theorem leaf_95_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T95_53
      hfix95_53 hinj95_53 hcardT95_53
      (fun i => conj_mem_of_fixedPoints _ _ (T95_53 i) (hfix95_53 i) _)
      ⟨95, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T95_53_2 Q2.hfix95_53_2 Q2.hinj95_53_2
      Q2.hcardT95_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_53_2 i) (Q2.hfix95_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T95_53 = colFn colCert_95_53_0.D (m := 25) from colCert_95_53_0.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 0 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T95_53_2 = colFn colCert_95_53_0.D (m := 25) from colCert_95_53_0.bind2]
  exact alnAll_95_53_0 j hj hq

theorem leaf_95_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T95_53
      hfix95_53 hinj95_53 hcardT95_53
      (fun i => conj_mem_of_fixedPoints _ _ (T95_53 i) (hfix95_53 i) _)
      ⟨95, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T95_53_2 Q2.hfix95_53_2 Q2.hinj95_53_2
      Q2.hcardT95_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_53_2 i) (Q2.hfix95_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T95_53 = colFn colCert_95_53_1.D (m := 25) from colCert_95_53_1.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 1 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T95_53_2 = colFn colCert_95_53_1.D (m := 25) from colCert_95_53_1.bind2]
  exact alnAll_95_53_1 j hj hq

theorem leaf_95_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T95_53
      hfix95_53 hinj95_53 hcardT95_53
      (fun i => conj_mem_of_fixedPoints _ _ (T95_53 i) (hfix95_53 i) _)
      ⟨95, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T95_53_2 Q2.hfix95_53_2 Q2.hinj95_53_2
      Q2.hcardT95_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_53_2 i) (Q2.hfix95_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T95_53 = colFn colCert_95_53_2.D (m := 25) from colCert_95_53_2.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 2 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T95_53_2 = colFn colCert_95_53_2.D (m := 25) from colCert_95_53_2.bind2]
  exact alnAll_95_53_2 j hj hq

theorem leaf_95_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T95_53
      hfix95_53 hinj95_53 hcardT95_53
      (fun i => conj_mem_of_fixedPoints _ _ (T95_53 i) (hfix95_53 i) _)
      ⟨95, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T95_53_2 Q2.hfix95_53_2 Q2.hinj95_53_2
      Q2.hcardT95_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_53_2 i) (Q2.hfix95_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T95_53 = colFn colCert_95_53_3.D (m := 25) from colCert_95_53_3.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 3 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T95_53_2 = colFn colCert_95_53_3.D (m := 25) from colCert_95_53_3.bind2]
  exact alnAll_95_53_3 j hj hq

theorem leaf_95_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T95_53
      hfix95_53 hinj95_53 hcardT95_53
      (fun i => conj_mem_of_fixedPoints _ _ (T95_53 i) (hfix95_53 i) _)
      ⟨95, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T95_53_2 Q2.hfix95_53_2 Q2.hinj95_53_2
      Q2.hcardT95_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_53_2 i) (Q2.hfix95_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T95_53 = colFn colCert_95_53_4.D (m := 25) from colCert_95_53_4.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 4 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T95_53_2 = colFn colCert_95_53_4.D (m := 25) from colCert_95_53_4.bind2]
  exact alnAll_95_53_4 j hj hq

theorem leaf_95_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T95_53
      hfix95_53 hinj95_53 hcardT95_53
      (fun i => conj_mem_of_fixedPoints _ _ (T95_53 i) (hfix95_53 i) _)
      ⟨95, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T95_53_2 Q2.hfix95_53_2 Q2.hinj95_53_2
      Q2.hcardT95_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_53_2 i) (Q2.hfix95_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T95_53 = colFn colCert_95_53_5.D (m := 25) from colCert_95_53_5.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 5 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T95_53_2 = colFn colCert_95_53_5.D (m := 25) from colCert_95_53_5.bind2]
  exact alnAll_95_53_5 j hj hq

theorem leaf_95_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T95_53
      hfix95_53 hinj95_53 hcardT95_53
      (fun i => conj_mem_of_fixedPoints _ _ (T95_53 i) (hfix95_53 i) _)
      ⟨95, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T95_53_2 Q2.hfix95_53_2 Q2.hinj95_53_2
      Q2.hcardT95_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_53_2 i) (Q2.hfix95_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T95_53 = colFn colCert_95_53_10.D (m := 25) from colCert_95_53_10.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 10 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T95_53_2 = colFn colCert_95_53_10.D (m := 25) from colCert_95_53_10.bind2]
  exact alnAll_95_53_10 j hj hq

theorem leaf_95_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T95_53
      hfix95_53 hinj95_53 hcardT95_53
      (fun i => conj_mem_of_fixedPoints _ _ (T95_53 i) (hfix95_53 i) _)
      ⟨95, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T95_53_2 Q2.hfix95_53_2 Q2.hinj95_53_2
      Q2.hcardT95_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_53_2 i) (Q2.hfix95_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T95_53 = colFn colCert_95_53_15.D (m := 25) from colCert_95_53_15.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 15 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T95_53_2 = colFn colCert_95_53_15.D (m := 25) from colCert_95_53_15.bind2]
  exact alnAll_95_53_15 j hj hq

theorem leaf_95_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T95_53
      hfix95_53 hinj95_53 hcardT95_53
      (fun i => conj_mem_of_fixedPoints _ _ (T95_53 i) (hfix95_53 i) _)
      ⟨95, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T95_53_2 Q2.hfix95_53_2 Q2.hinj95_53_2
      Q2.hcardT95_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_53_2 i) (Q2.hfix95_53_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp) : ↥(reps ⟨53, by decide⟩)) : Coordinate 1)
        T95_53 = colFn colCert_95_53_20.D (m := 25) from colCert_95_53_20.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨53, by decide⟩ 20 hp : ↥(Q2.reps ⟨53, by decide⟩)) : Coordinate 2)
        Q2.T95_53_2 = colFn colCert_95_53_20.D (m := 25) from colCert_95_53_20.bind2]
  exact alnAll_95_53_20 j hj hq

theorem leaf_95_95_0 (hp : 0 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 0 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 0 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_0.D (m := 25) from colCert_95_95_0.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 0 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_0.D (m := 25) from colCert_95_95_0.bind2]
  exact alnAll_95_95_0 j hj hq

theorem leaf_95_95_1 (hp : 1 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 1 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 1 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_1.D (m := 25) from colCert_95_95_1.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 1 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_1.D (m := 25) from colCert_95_95_1.bind2]
  exact alnAll_95_95_1 j hj hq

theorem leaf_95_95_2 (hp : 2 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 95 []).length)
    (hq : (normIsRep.getD 95 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 2 hp)
        (rowE2 (⟨95, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp))
        (rowE1 (⟨95, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨95, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨95, by decide⟩ (listedAt ⟨95, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp)) T95_95
      hfix95_95 hinj95_95 hcardT95_95
      (fun i => conj_mem_of_fixedPoints _ _ (T95_95 i) (hfix95_95 i) _)
      ⟨95, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨95, by decide⟩ (Q2.listedAt ⟨95, by decide⟩
        (alnCheck_rep ⟨95, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 2 hp) Q2.T95_95_2 Q2.hfix95_95_2 Q2.hinj95_95_2
      Q2.hcardT95_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T95_95_2 i) (Q2.hfix95_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨95, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T95_95 = colFn colCert_95_95_2.D (m := 25) from colCert_95_95_2.bind1,
    show colData2 (⟨95, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 2 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T95_95_2 = colFn colCert_95_95_2.D (m := 25) from colCert_95_95_2.bind2]
  exact alnAll_95_95_2 j hj hq

end LeanDring.P5Presentation
