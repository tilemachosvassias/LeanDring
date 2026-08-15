/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C001
import LeanDring.P5.Data.ColCdd.C002
import LeanDring.P5.Data.ColCdd.C003
import LeanDring.P5.Data.ColRestCheap.C017
import LeanDring.P5.Data.ColRestCheap.C018
import LeanDring.P5.Data.ColRestCheap.C019
import LeanDring.P5.Data.ColRestCheap.C020
import LeanDring.P5.Data.ColTau.C001
import LeanDring.P5.Data.EntryK.C024
import LeanDring.P5.Data.EntryK.C025
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C031
import LeanDring.P5.Data.SpeciesDiv.C007
import LeanDring.P5.Data.SpeciesDiv.C008
import LeanDring.P5.Data.SpeciesDiv.C009
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk02

/-! # Stage-5 leaves, chunk 21 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_115_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T115_54
      hfix115_54 hinj115_54 hcardT115_54
      (fun i => conj_mem_of_fixedPoints _ _ (T115_54 i) (hfix115_54 i) _)
      ⟨115, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T115_54_2 Q2.hfix115_54_2 Q2.hinj115_54_2
      Q2.hcardT115_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_54_2 i) (Q2.hfix115_54_2 i) _)
      colCert_115_54_1.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T115_54
      hfix115_54 hinj115_54 hcardT115_54
      (fun i => conj_mem_of_fixedPoints _ _ (T115_54 i) (hfix115_54 i) _)
      ⟨115, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T115_54_2 Q2.hfix115_54_2 Q2.hinj115_54_2
      Q2.hcardT115_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_54_2 i) (Q2.hfix115_54_2 i) _)
      colCert_115_54_2.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T115_54
      hfix115_54 hinj115_54 hcardT115_54
      (fun i => conj_mem_of_fixedPoints _ _ (T115_54 i) (hfix115_54 i) _)
      ⟨115, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T115_54_2 Q2.hfix115_54_2 Q2.hinj115_54_2
      Q2.hcardT115_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_54_2 i) (Q2.hfix115_54_2 i) _)
      colCert_115_54_3.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T115_54
      hfix115_54 hinj115_54 hcardT115_54
      (fun i => conj_mem_of_fixedPoints _ _ (T115_54 i) (hfix115_54 i) _)
      ⟨115, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T115_54_2 Q2.hfix115_54_2 Q2.hinj115_54_2
      Q2.hcardT115_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_54_2 i) (Q2.hfix115_54_2 i) _)
      colCert_115_54_4.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T115_54
      hfix115_54 hinj115_54 hcardT115_54
      (fun i => conj_mem_of_fixedPoints _ _ (T115_54 i) (hfix115_54 i) _)
      ⟨115, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T115_54_2 Q2.hfix115_54_2 Q2.hinj115_54_2
      Q2.hcardT115_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_54_2 i) (Q2.hfix115_54_2 i) _)
      colCert_115_54_5.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T115_54
      hfix115_54 hinj115_54 hcardT115_54
      (fun i => conj_mem_of_fixedPoints _ _ (T115_54 i) (hfix115_54 i) _)
      ⟨115, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T115_54_2 Q2.hfix115_54_2 Q2.hinj115_54_2
      Q2.hcardT115_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_54_2 i) (Q2.hfix115_54_2 i) _)
      colCert_115_54_10.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T115_54
      hfix115_54 hinj115_54 hcardT115_54
      (fun i => conj_mem_of_fixedPoints _ _ (T115_54 i) (hfix115_54 i) _)
      ⟨115, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T115_54_2 Q2.hfix115_54_2 Q2.hinj115_54_2
      Q2.hcardT115_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_54_2 i) (Q2.hfix115_54_2 i) _)
      colCert_115_54_15.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T115_54
      hfix115_54 hinj115_54 hcardT115_54
      (fun i => conj_mem_of_fixedPoints _ _ (T115_54 i) (hfix115_54 i) _)
      ⟨115, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T115_54_2 Q2.hfix115_54_2 Q2.hinj115_54_2
      Q2.hcardT115_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_54_2 i) (Q2.hfix115_54_2 i) _)
      colCert_115_54_20.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_115_0 (hp : 0 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 0 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp)) T115_115
      hfix115_115 hinj115_115 hcardT115_115
      (fun i => conj_mem_of_fixedPoints _ _ (T115_115 i) (hfix115_115 i) _)
      ⟨115, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 0 hp) Q2.T115_115_2 Q2.hfix115_115_2 Q2.hinj115_115_2
      Q2.hcardT115_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_115_2 i) (Q2.hfix115_115_2 i) _)
      colCert_115_115_0.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_115_1 (hp : 1 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 1 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp)) T115_115
      hfix115_115 hinj115_115 hcardT115_115
      (fun i => conj_mem_of_fixedPoints _ _ (T115_115 i) (hfix115_115 i) _)
      ⟨115, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 1 hp) Q2.T115_115_2 Q2.hfix115_115_2 Q2.hinj115_115_2
      Q2.hcardT115_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_115_2 i) (Q2.hfix115_115_2 i) _)
      colCert_115_115_1.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_115_2 (hp : 2 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 2 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp)) T115_115
      hfix115_115 hinj115_115 hcardT115_115
      (fun i => conj_mem_of_fixedPoints _ _ (T115_115 i) (hfix115_115 i) _)
      ⟨115, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 2 hp) Q2.T115_115_2 Q2.hfix115_115_2 Q2.hinj115_115_2
      Q2.hcardT115_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_115_2 i) (Q2.hfix115_115_2 i) _)
      colCert_115_115_2.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_115_3 (hp : 3 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 3 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp)) T115_115
      hfix115_115 hinj115_115 hcardT115_115
      (fun i => conj_mem_of_fixedPoints _ _ (T115_115 i) (hfix115_115 i) _)
      ⟨115, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 3 hp) Q2.T115_115_2 Q2.hfix115_115_2 Q2.hinj115_115_2
      Q2.hcardT115_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_115_2 i) (Q2.hfix115_115_2 i) _)
      colCert_115_115_3.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_115_4 (hp : 4 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 4 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp)) T115_115
      hfix115_115 hinj115_115 hcardT115_115
      (fun i => conj_mem_of_fixedPoints _ _ (T115_115 i) (hfix115_115 i) _)
      ⟨115, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 4 hp) Q2.T115_115_2 Q2.hfix115_115_2 Q2.hinj115_115_2
      Q2.hcardT115_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_115_2 i) (Q2.hfix115_115_2 i) _)
      colCert_115_115_4.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_115_5 (hp : 5 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 5 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp)) T115_115
      hfix115_115 hinj115_115 hcardT115_115
      (fun i => conj_mem_of_fixedPoints _ _ (T115_115 i) (hfix115_115 i) _)
      ⟨115, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 5 hp) Q2.T115_115_2 Q2.hfix115_115_2 Q2.hinj115_115_2
      Q2.hcardT115_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_115_2 i) (Q2.hfix115_115_2 i) _)
      colCert_115_115_5.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_115_10 (hp : 10 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 10 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp)) T115_115
      hfix115_115 hinj115_115 hcardT115_115
      (fun i => conj_mem_of_fixedPoints _ _ (T115_115 i) (hfix115_115 i) _)
      ⟨115, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 10 hp) Q2.T115_115_2 Q2.hfix115_115_2 Q2.hinj115_115_2
      Q2.hcardT115_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_115_2 i) (Q2.hfix115_115_2 i) _)
      colCert_115_115_10.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_115_15 (hp : 15 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 15 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp)) T115_115
      hfix115_115 hinj115_115 hcardT115_115
      (fun i => conj_mem_of_fixedPoints _ _ (T115_115 i) (hfix115_115 i) _)
      ⟨115, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 15 hp) Q2.T115_115_2 Q2.hfix115_115_2 Q2.hinj115_115_2
      Q2.hcardT115_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_115_2 i) (Q2.hfix115_115_2 i) _)
      colCert_115_115_15.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_115_115_20 (hp : 20 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 115 []).length)
    (hq : (normIsRep.getD 115 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 20 hp)
        (rowE2 (⟨115, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp))
        (rowE1 (⟨115, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨115, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨115, by decide⟩ (listedAt ⟨115, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp)) T115_115
      hfix115_115 hinj115_115 hcardT115_115
      (fun i => conj_mem_of_fixedPoints _ _ (T115_115 i) (hfix115_115 i) _)
      ⟨115, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨115, by decide⟩ (Q2.listedAt ⟨115, by decide⟩
        (alnCheck_rep ⟨115, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 20 hp) Q2.T115_115_2 Q2.hfix115_115_2 Q2.hinj115_115_2
      Q2.hcardT115_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T115_115_2 i) (Q2.hfix115_115_2 i) _)
      colCert_115_115_20.hD ?_).symm
  rw [alnId_115 j hj]


theorem leaf_116_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T116_1
      hfix116_1 hinj116_1 hcardT116_1
      (fun i => conj_mem_of_fixedPoints _ _ (T116_1 i) (hfix116_1 i) _)
      ⟨116, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T116_1_2 Q2.hfix116_1_2 Q2.hinj116_1_2
      Q2.hcardT116_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_1_2 i) (Q2.hfix116_1_2 i) _)
      colCert_116_1_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T116_1
      hfix116_1 hinj116_1 hcardT116_1
      (fun i => conj_mem_of_fixedPoints _ _ (T116_1 i) (hfix116_1 i) _)
      ⟨116, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T116_1_2 Q2.hfix116_1_2 Q2.hinj116_1_2
      Q2.hcardT116_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_1_2 i) (Q2.hfix116_1_2 i) _)
      colCert_116_1_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T116_1
      hfix116_1 hinj116_1 hcardT116_1
      (fun i => conj_mem_of_fixedPoints _ _ (T116_1 i) (hfix116_1 i) _)
      ⟨116, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T116_1_2 Q2.hfix116_1_2 Q2.hinj116_1_2
      Q2.hcardT116_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_1_2 i) (Q2.hfix116_1_2 i) _)
      colCert_116_1_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T116_1
      hfix116_1 hinj116_1 hcardT116_1
      (fun i => conj_mem_of_fixedPoints _ _ (T116_1 i) (hfix116_1 i) _)
      ⟨116, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T116_1_2 Q2.hfix116_1_2 Q2.hinj116_1_2
      Q2.hcardT116_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_1_2 i) (Q2.hfix116_1_2 i) _)
      colCert_116_1_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T116_1
      hfix116_1 hinj116_1 hcardT116_1
      (fun i => conj_mem_of_fixedPoints _ _ (T116_1 i) (hfix116_1 i) _)
      ⟨116, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T116_1_2 Q2.hfix116_1_2 Q2.hinj116_1_2
      Q2.hcardT116_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_1_2 i) (Q2.hfix116_1_2 i) _)
      colCert_116_1_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T116_6
      hfix116_6 hinj116_6 hcardT116_6
      (fun i => conj_mem_of_fixedPoints _ _ (T116_6 i) (hfix116_6 i) _)
      ⟨116, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T116_6_2 Q2.hfix116_6_2 Q2.hinj116_6_2
      Q2.hcardT116_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_6_2 i) (Q2.hfix116_6_2 i) _)
      colCert_116_6_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T116_6
      hfix116_6 hinj116_6 hcardT116_6
      (fun i => conj_mem_of_fixedPoints _ _ (T116_6 i) (hfix116_6 i) _)
      ⟨116, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T116_6_2 Q2.hfix116_6_2 Q2.hinj116_6_2
      Q2.hcardT116_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_6_2 i) (Q2.hfix116_6_2 i) _)
      colCert_116_6_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T116_6
      hfix116_6 hinj116_6 hcardT116_6
      (fun i => conj_mem_of_fixedPoints _ _ (T116_6 i) (hfix116_6 i) _)
      ⟨116, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T116_6_2 Q2.hfix116_6_2 Q2.hinj116_6_2
      Q2.hcardT116_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_6_2 i) (Q2.hfix116_6_2 i) _)
      colCert_116_6_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T116_6
      hfix116_6 hinj116_6 hcardT116_6
      (fun i => conj_mem_of_fixedPoints _ _ (T116_6 i) (hfix116_6 i) _)
      ⟨116, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T116_6_2 Q2.hfix116_6_2 Q2.hinj116_6_2
      Q2.hcardT116_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_6_2 i) (Q2.hfix116_6_2 i) _)
      colCert_116_6_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T116_6
      hfix116_6 hinj116_6 hcardT116_6
      (fun i => conj_mem_of_fixedPoints _ _ (T116_6 i) (hfix116_6 i) _)
      ⟨116, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T116_6_2 Q2.hfix116_6_2 Q2.hinj116_6_2
      Q2.hcardT116_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_6_2 i) (Q2.hfix116_6_2 i) _)
      colCert_116_6_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T116_7
      hfix116_7 hinj116_7 hcardT116_7
      (fun i => conj_mem_of_fixedPoints _ _ (T116_7 i) (hfix116_7 i) _)
      ⟨116, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T116_7_2 Q2.hfix116_7_2 Q2.hinj116_7_2
      Q2.hcardT116_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_7_2 i) (Q2.hfix116_7_2 i) _)
      colCert_116_7_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T116_7
      hfix116_7 hinj116_7 hcardT116_7
      (fun i => conj_mem_of_fixedPoints _ _ (T116_7 i) (hfix116_7 i) _)
      ⟨116, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T116_7_2 Q2.hfix116_7_2 Q2.hinj116_7_2
      Q2.hcardT116_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_7_2 i) (Q2.hfix116_7_2 i) _)
      colCert_116_7_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T116_7
      hfix116_7 hinj116_7 hcardT116_7
      (fun i => conj_mem_of_fixedPoints _ _ (T116_7 i) (hfix116_7 i) _)
      ⟨116, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T116_7_2 Q2.hfix116_7_2 Q2.hinj116_7_2
      Q2.hcardT116_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_7_2 i) (Q2.hfix116_7_2 i) _)
      colCert_116_7_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T116_7
      hfix116_7 hinj116_7 hcardT116_7
      (fun i => conj_mem_of_fixedPoints _ _ (T116_7 i) (hfix116_7 i) _)
      ⟨116, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T116_7_2 Q2.hfix116_7_2 Q2.hinj116_7_2
      Q2.hcardT116_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_7_2 i) (Q2.hfix116_7_2 i) _)
      colCert_116_7_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T116_7
      hfix116_7 hinj116_7 hcardT116_7
      (fun i => conj_mem_of_fixedPoints _ _ (T116_7 i) (hfix116_7 i) _)
      ⟨116, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T116_7_2 Q2.hfix116_7_2 Q2.hinj116_7_2
      Q2.hcardT116_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_7_2 i) (Q2.hfix116_7_2 i) _)
      colCert_116_7_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T116_8
      hfix116_8 hinj116_8 hcardT116_8
      (fun i => conj_mem_of_fixedPoints _ _ (T116_8 i) (hfix116_8 i) _)
      ⟨116, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T116_8_2 Q2.hfix116_8_2 Q2.hinj116_8_2
      Q2.hcardT116_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_8_2 i) (Q2.hfix116_8_2 i) _)
      colCert_116_8_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T116_8
      hfix116_8 hinj116_8 hcardT116_8
      (fun i => conj_mem_of_fixedPoints _ _ (T116_8 i) (hfix116_8 i) _)
      ⟨116, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T116_8_2 Q2.hfix116_8_2 Q2.hinj116_8_2
      Q2.hcardT116_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_8_2 i) (Q2.hfix116_8_2 i) _)
      colCert_116_8_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T116_8
      hfix116_8 hinj116_8 hcardT116_8
      (fun i => conj_mem_of_fixedPoints _ _ (T116_8 i) (hfix116_8 i) _)
      ⟨116, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T116_8_2 Q2.hfix116_8_2 Q2.hinj116_8_2
      Q2.hcardT116_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_8_2 i) (Q2.hfix116_8_2 i) _)
      colCert_116_8_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T116_8
      hfix116_8 hinj116_8 hcardT116_8
      (fun i => conj_mem_of_fixedPoints _ _ (T116_8 i) (hfix116_8 i) _)
      ⟨116, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T116_8_2 Q2.hfix116_8_2 Q2.hinj116_8_2
      Q2.hcardT116_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_8_2 i) (Q2.hfix116_8_2 i) _)
      colCert_116_8_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T116_8
      hfix116_8 hinj116_8 hcardT116_8
      (fun i => conj_mem_of_fixedPoints _ _ (T116_8 i) (hfix116_8 i) _)
      ⟨116, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T116_8_2 Q2.hfix116_8_2 Q2.hinj116_8_2
      Q2.hcardT116_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_8_2 i) (Q2.hfix116_8_2 i) _)
      colCert_116_8_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T116_9
      hfix116_9 hinj116_9 hcardT116_9
      (fun i => conj_mem_of_fixedPoints _ _ (T116_9 i) (hfix116_9 i) _)
      ⟨116, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T116_9_2 Q2.hfix116_9_2 Q2.hinj116_9_2
      Q2.hcardT116_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_9_2 i) (Q2.hfix116_9_2 i) _)
      colCert_116_9_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T116_9
      hfix116_9 hinj116_9 hcardT116_9
      (fun i => conj_mem_of_fixedPoints _ _ (T116_9 i) (hfix116_9 i) _)
      ⟨116, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T116_9_2 Q2.hfix116_9_2 Q2.hinj116_9_2
      Q2.hcardT116_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_9_2 i) (Q2.hfix116_9_2 i) _)
      colCert_116_9_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T116_9
      hfix116_9 hinj116_9 hcardT116_9
      (fun i => conj_mem_of_fixedPoints _ _ (T116_9 i) (hfix116_9 i) _)
      ⟨116, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T116_9_2 Q2.hfix116_9_2 Q2.hinj116_9_2
      Q2.hcardT116_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_9_2 i) (Q2.hfix116_9_2 i) _)
      colCert_116_9_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T116_9
      hfix116_9 hinj116_9 hcardT116_9
      (fun i => conj_mem_of_fixedPoints _ _ (T116_9 i) (hfix116_9 i) _)
      ⟨116, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T116_9_2 Q2.hfix116_9_2 Q2.hinj116_9_2
      Q2.hcardT116_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_9_2 i) (Q2.hfix116_9_2 i) _)
      colCert_116_9_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T116_9
      hfix116_9 hinj116_9 hcardT116_9
      (fun i => conj_mem_of_fixedPoints _ _ (T116_9 i) (hfix116_9 i) _)
      ⟨116, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T116_9_2 Q2.hfix116_9_2 Q2.hinj116_9_2
      Q2.hcardT116_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_9_2 i) (Q2.hfix116_9_2 i) _)
      colCert_116_9_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T116_10
      hfix116_10 hinj116_10 hcardT116_10
      (fun i => conj_mem_of_fixedPoints _ _ (T116_10 i) (hfix116_10 i) _)
      ⟨116, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T116_10_2 Q2.hfix116_10_2 Q2.hinj116_10_2
      Q2.hcardT116_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_10_2 i) (Q2.hfix116_10_2 i) _)
      colCert_116_10_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T116_10
      hfix116_10 hinj116_10 hcardT116_10
      (fun i => conj_mem_of_fixedPoints _ _ (T116_10 i) (hfix116_10 i) _)
      ⟨116, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T116_10_2 Q2.hfix116_10_2 Q2.hinj116_10_2
      Q2.hcardT116_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_10_2 i) (Q2.hfix116_10_2 i) _)
      colCert_116_10_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T116_10
      hfix116_10 hinj116_10 hcardT116_10
      (fun i => conj_mem_of_fixedPoints _ _ (T116_10 i) (hfix116_10 i) _)
      ⟨116, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T116_10_2 Q2.hfix116_10_2 Q2.hinj116_10_2
      Q2.hcardT116_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_10_2 i) (Q2.hfix116_10_2 i) _)
      colCert_116_10_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T116_10
      hfix116_10 hinj116_10 hcardT116_10
      (fun i => conj_mem_of_fixedPoints _ _ (T116_10 i) (hfix116_10 i) _)
      ⟨116, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T116_10_2 Q2.hfix116_10_2 Q2.hinj116_10_2
      Q2.hcardT116_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_10_2 i) (Q2.hfix116_10_2 i) _)
      colCert_116_10_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T116_10
      hfix116_10 hinj116_10 hcardT116_10
      (fun i => conj_mem_of_fixedPoints _ _ (T116_10 i) (hfix116_10 i) _)
      ⟨116, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T116_10_2 Q2.hfix116_10_2 Q2.hinj116_10_2
      Q2.hcardT116_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_10_2 i) (Q2.hfix116_10_2 i) _)
      colCert_116_10_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T116_12
      hfix116_12 hinj116_12 hcardT116_12
      (fun i => conj_mem_of_fixedPoints _ _ (T116_12 i) (hfix116_12 i) _)
      ⟨116, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T116_12_2 Q2.hfix116_12_2 Q2.hinj116_12_2
      Q2.hcardT116_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_12_2 i) (Q2.hfix116_12_2 i) _)
      colCert_116_12_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T116_12
      hfix116_12 hinj116_12 hcardT116_12
      (fun i => conj_mem_of_fixedPoints _ _ (T116_12 i) (hfix116_12 i) _)
      ⟨116, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T116_12_2 Q2.hfix116_12_2 Q2.hinj116_12_2
      Q2.hcardT116_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_12_2 i) (Q2.hfix116_12_2 i) _)
      colCert_116_12_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T116_12
      hfix116_12 hinj116_12 hcardT116_12
      (fun i => conj_mem_of_fixedPoints _ _ (T116_12 i) (hfix116_12 i) _)
      ⟨116, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T116_12_2 Q2.hfix116_12_2 Q2.hinj116_12_2
      Q2.hcardT116_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_12_2 i) (Q2.hfix116_12_2 i) _)
      colCert_116_12_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T116_12
      hfix116_12 hinj116_12 hcardT116_12
      (fun i => conj_mem_of_fixedPoints _ _ (T116_12 i) (hfix116_12 i) _)
      ⟨116, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T116_12_2 Q2.hfix116_12_2 Q2.hinj116_12_2
      Q2.hcardT116_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_12_2 i) (Q2.hfix116_12_2 i) _)
      colCert_116_12_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T116_12
      hfix116_12 hinj116_12 hcardT116_12
      (fun i => conj_mem_of_fixedPoints _ _ (T116_12 i) (hfix116_12 i) _)
      ⟨116, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T116_12_2 Q2.hfix116_12_2 Q2.hinj116_12_2
      Q2.hcardT116_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_12_2 i) (Q2.hfix116_12_2 i) _)
      colCert_116_12_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_0 (hp : 0 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 0 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_1 (hp : 1 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 1 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_2 (hp : 2 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 2 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_3 (hp : 3 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 3 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_4 (hp : 4 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 4 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_5 (hp : 5 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 5 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T116_13 = colFn colCertDiv_116_13_5.D1 (m := 5) from colCertDiv_116_13_5.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 5 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T116_13_2 = colFn colCertDiv_116_13_5.D2 (m := 5) from colCertDiv_116_13_5.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_tau ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_13_5_tau_match


theorem leaf_116_13_6 (hp : 6 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 6 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 6 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T116_13 = colFn colCertDiv_116_13_6.D1 (m := 5) from colCertDiv_116_13_6.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 6 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T116_13_2 = colFn colCertDiv_116_13_6.D2 (m := 5) from colCertDiv_116_13_6.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_tau ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_13_6_tau_match


theorem leaf_116_13_7 (hp : 7 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 7 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 7 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T116_13 = colFn colCertDiv_116_13_7.D1 (m := 5) from colCertDiv_116_13_7.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 7 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T116_13_2 = colFn colCertDiv_116_13_7.D2 (m := 5) from colCertDiv_116_13_7.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_tau ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_13_7_tau_match


theorem leaf_116_13_8 (hp : 8 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 8 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 8 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T116_13 = colFn colCertDiv_116_13_8.D1 (m := 5) from colCertDiv_116_13_8.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 8 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T116_13_2 = colFn colCertDiv_116_13_8.D2 (m := 5) from colCertDiv_116_13_8.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_tau ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_13_8_tau_match


theorem leaf_116_13_9 (hp : 9 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 9 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 9 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_9.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_10 (hp : 10 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 10 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_11 (hp : 11 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 11 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 11 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_11.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_12 (hp : 12 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 12 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 12 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_12.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_13 (hp : 13 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 13 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 13 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_13.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_14 (hp : 14 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 14 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 14 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_14.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_15 (hp : 15 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 15 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_16 (hp : 16 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 16 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 16 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_16.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_17 (hp : 17 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 17 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 17 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_17.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_18 (hp : 18 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 18 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 18 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_18.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_19 (hp : 19 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 19 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 19 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_19.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_20 (hp : 20 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 20 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_21 (hp : 21 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 21 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 21 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_21.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_22 (hp : 22 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 22 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 22 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_22.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_23 (hp : 23 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 23 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 23 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_23.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_13_24 (hp : 24 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 24 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp)) T116_13
      hfix116_13 hinj116_13 hcardT116_13
      (fun i => conj_mem_of_fixedPoints _ _ (T116_13 i) (hfix116_13 i) _)
      ⟨116, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 24 hp) Q2.T116_13_2 Q2.hfix116_13_2 Q2.hinj116_13_2
      Q2.hcardT116_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_13_2 i) (Q2.hfix116_13_2 i) _)
      colCert_116_13_24.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T116_19
      hfix116_19 hinj116_19 hcardT116_19
      (fun i => conj_mem_of_fixedPoints _ _ (T116_19 i) (hfix116_19 i) _)
      ⟨116, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T116_19_2 Q2.hfix116_19_2 Q2.hinj116_19_2
      Q2.hcardT116_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_19_2 i) (Q2.hfix116_19_2 i) _)
      colCert_116_19_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T116_19
      hfix116_19 hinj116_19 hcardT116_19
      (fun i => conj_mem_of_fixedPoints _ _ (T116_19 i) (hfix116_19 i) _)
      ⟨116, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T116_19_2 Q2.hfix116_19_2 Q2.hinj116_19_2
      Q2.hcardT116_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_19_2 i) (Q2.hfix116_19_2 i) _)
      colCert_116_19_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T116_19
      hfix116_19 hinj116_19 hcardT116_19
      (fun i => conj_mem_of_fixedPoints _ _ (T116_19 i) (hfix116_19 i) _)
      ⟨116, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T116_19_2 Q2.hfix116_19_2 Q2.hinj116_19_2
      Q2.hcardT116_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_19_2 i) (Q2.hfix116_19_2 i) _)
      colCert_116_19_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T116_19
      hfix116_19 hinj116_19 hcardT116_19
      (fun i => conj_mem_of_fixedPoints _ _ (T116_19 i) (hfix116_19 i) _)
      ⟨116, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T116_19_2 Q2.hfix116_19_2 Q2.hinj116_19_2
      Q2.hcardT116_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_19_2 i) (Q2.hfix116_19_2 i) _)
      colCert_116_19_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T116_19
      hfix116_19 hinj116_19 hcardT116_19
      (fun i => conj_mem_of_fixedPoints _ _ (T116_19 i) (hfix116_19 i) _)
      ⟨116, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T116_19_2 Q2.hfix116_19_2 Q2.hinj116_19_2
      Q2.hcardT116_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_19_2 i) (Q2.hfix116_19_2 i) _)
      colCert_116_19_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T116_19
      hfix116_19 hinj116_19 hcardT116_19
      (fun i => conj_mem_of_fixedPoints _ _ (T116_19 i) (hfix116_19 i) _)
      ⟨116, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T116_19_2 Q2.hfix116_19_2 Q2.hinj116_19_2
      Q2.hcardT116_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_19_2 i) (Q2.hfix116_19_2 i) _)
      colCert_116_19_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T116_19
      hfix116_19 hinj116_19 hcardT116_19
      (fun i => conj_mem_of_fixedPoints _ _ (T116_19 i) (hfix116_19 i) _)
      ⟨116, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T116_19_2 Q2.hfix116_19_2 Q2.hinj116_19_2
      Q2.hcardT116_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_19_2 i) (Q2.hfix116_19_2 i) _)
      colCert_116_19_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T116_19
      hfix116_19 hinj116_19 hcardT116_19
      (fun i => conj_mem_of_fixedPoints _ _ (T116_19 i) (hfix116_19 i) _)
      ⟨116, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T116_19_2 Q2.hfix116_19_2 Q2.hinj116_19_2
      Q2.hcardT116_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_19_2 i) (Q2.hfix116_19_2 i) _)
      colCert_116_19_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T116_19
      hfix116_19 hinj116_19 hcardT116_19
      (fun i => conj_mem_of_fixedPoints _ _ (T116_19 i) (hfix116_19 i) _)
      ⟨116, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T116_19_2 Q2.hfix116_19_2 Q2.hinj116_19_2
      Q2.hcardT116_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_19_2 i) (Q2.hfix116_19_2 i) _)
      colCert_116_19_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T116_24
      hfix116_24 hinj116_24 hcardT116_24
      (fun i => conj_mem_of_fixedPoints _ _ (T116_24 i) (hfix116_24 i) _)
      ⟨116, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T116_24_2 Q2.hfix116_24_2 Q2.hinj116_24_2
      Q2.hcardT116_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_24_2 i) (Q2.hfix116_24_2 i) _)
      colCert_116_24_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T116_24
      hfix116_24 hinj116_24 hcardT116_24
      (fun i => conj_mem_of_fixedPoints _ _ (T116_24 i) (hfix116_24 i) _)
      ⟨116, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T116_24_2 Q2.hfix116_24_2 Q2.hinj116_24_2
      Q2.hcardT116_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_24_2 i) (Q2.hfix116_24_2 i) _)
      colCert_116_24_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T116_24
      hfix116_24 hinj116_24 hcardT116_24
      (fun i => conj_mem_of_fixedPoints _ _ (T116_24 i) (hfix116_24 i) _)
      ⟨116, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T116_24_2 Q2.hfix116_24_2 Q2.hinj116_24_2
      Q2.hcardT116_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_24_2 i) (Q2.hfix116_24_2 i) _)
      colCert_116_24_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T116_24
      hfix116_24 hinj116_24 hcardT116_24
      (fun i => conj_mem_of_fixedPoints _ _ (T116_24 i) (hfix116_24 i) _)
      ⟨116, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T116_24_2 Q2.hfix116_24_2 Q2.hinj116_24_2
      Q2.hcardT116_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_24_2 i) (Q2.hfix116_24_2 i) _)
      colCert_116_24_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T116_24
      hfix116_24 hinj116_24 hcardT116_24
      (fun i => conj_mem_of_fixedPoints _ _ (T116_24 i) (hfix116_24 i) _)
      ⟨116, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T116_24_2 Q2.hfix116_24_2 Q2.hinj116_24_2
      Q2.hcardT116_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_24_2 i) (Q2.hfix116_24_2 i) _)
      colCert_116_24_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T116_24
      hfix116_24 hinj116_24 hcardT116_24
      (fun i => conj_mem_of_fixedPoints _ _ (T116_24 i) (hfix116_24 i) _)
      ⟨116, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T116_24_2 Q2.hfix116_24_2 Q2.hinj116_24_2
      Q2.hcardT116_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_24_2 i) (Q2.hfix116_24_2 i) _)
      colCert_116_24_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T116_24
      hfix116_24 hinj116_24 hcardT116_24
      (fun i => conj_mem_of_fixedPoints _ _ (T116_24 i) (hfix116_24 i) _)
      ⟨116, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T116_24_2 Q2.hfix116_24_2 Q2.hinj116_24_2
      Q2.hcardT116_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_24_2 i) (Q2.hfix116_24_2 i) _)
      colCert_116_24_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T116_24
      hfix116_24 hinj116_24 hcardT116_24
      (fun i => conj_mem_of_fixedPoints _ _ (T116_24 i) (hfix116_24 i) _)
      ⟨116, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T116_24_2 Q2.hfix116_24_2 Q2.hinj116_24_2
      Q2.hcardT116_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_24_2 i) (Q2.hfix116_24_2 i) _)
      colCert_116_24_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T116_24
      hfix116_24 hinj116_24 hcardT116_24
      (fun i => conj_mem_of_fixedPoints _ _ (T116_24 i) (hfix116_24 i) _)
      ⟨116, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T116_24_2 Q2.hfix116_24_2 Q2.hinj116_24_2
      Q2.hcardT116_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_24_2 i) (Q2.hfix116_24_2 i) _)
      colCert_116_24_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T116_25
      hfix116_25 hinj116_25 hcardT116_25
      (fun i => conj_mem_of_fixedPoints _ _ (T116_25 i) (hfix116_25 i) _)
      ⟨116, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T116_25_2 Q2.hfix116_25_2 Q2.hinj116_25_2
      Q2.hcardT116_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_25_2 i) (Q2.hfix116_25_2 i) _)
      colCert_116_25_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T116_25
      hfix116_25 hinj116_25 hcardT116_25
      (fun i => conj_mem_of_fixedPoints _ _ (T116_25 i) (hfix116_25 i) _)
      ⟨116, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T116_25_2 Q2.hfix116_25_2 Q2.hinj116_25_2
      Q2.hcardT116_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_25_2 i) (Q2.hfix116_25_2 i) _)
      colCert_116_25_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T116_25
      hfix116_25 hinj116_25 hcardT116_25
      (fun i => conj_mem_of_fixedPoints _ _ (T116_25 i) (hfix116_25 i) _)
      ⟨116, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T116_25_2 Q2.hfix116_25_2 Q2.hinj116_25_2
      Q2.hcardT116_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_25_2 i) (Q2.hfix116_25_2 i) _)
      colCert_116_25_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T116_25
      hfix116_25 hinj116_25 hcardT116_25
      (fun i => conj_mem_of_fixedPoints _ _ (T116_25 i) (hfix116_25 i) _)
      ⟨116, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T116_25_2 Q2.hfix116_25_2 Q2.hinj116_25_2
      Q2.hcardT116_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_25_2 i) (Q2.hfix116_25_2 i) _)
      colCert_116_25_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T116_25
      hfix116_25 hinj116_25 hcardT116_25
      (fun i => conj_mem_of_fixedPoints _ _ (T116_25 i) (hfix116_25 i) _)
      ⟨116, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T116_25_2 Q2.hfix116_25_2 Q2.hinj116_25_2
      Q2.hcardT116_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_25_2 i) (Q2.hfix116_25_2 i) _)
      colCert_116_25_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T116_25
      hfix116_25 hinj116_25 hcardT116_25
      (fun i => conj_mem_of_fixedPoints _ _ (T116_25 i) (hfix116_25 i) _)
      ⟨116, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T116_25_2 Q2.hfix116_25_2 Q2.hinj116_25_2
      Q2.hcardT116_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_25_2 i) (Q2.hfix116_25_2 i) _)
      colCert_116_25_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T116_25
      hfix116_25 hinj116_25 hcardT116_25
      (fun i => conj_mem_of_fixedPoints _ _ (T116_25 i) (hfix116_25 i) _)
      ⟨116, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T116_25_2 Q2.hfix116_25_2 Q2.hinj116_25_2
      Q2.hcardT116_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_25_2 i) (Q2.hfix116_25_2 i) _)
      colCert_116_25_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T116_25
      hfix116_25 hinj116_25 hcardT116_25
      (fun i => conj_mem_of_fixedPoints _ _ (T116_25 i) (hfix116_25 i) _)
      ⟨116, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T116_25_2 Q2.hfix116_25_2 Q2.hinj116_25_2
      Q2.hcardT116_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_25_2 i) (Q2.hfix116_25_2 i) _)
      colCert_116_25_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T116_25
      hfix116_25 hinj116_25 hcardT116_25
      (fun i => conj_mem_of_fixedPoints _ _ (T116_25 i) (hfix116_25 i) _)
      ⟨116, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T116_25_2 Q2.hfix116_25_2 Q2.hinj116_25_2
      Q2.hcardT116_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_25_2 i) (Q2.hfix116_25_2 i) _)
      colCert_116_25_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T116_26
      hfix116_26 hinj116_26 hcardT116_26
      (fun i => conj_mem_of_fixedPoints _ _ (T116_26 i) (hfix116_26 i) _)
      ⟨116, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T116_26_2 Q2.hfix116_26_2 Q2.hinj116_26_2
      Q2.hcardT116_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_26_2 i) (Q2.hfix116_26_2 i) _)
      colCert_116_26_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T116_26
      hfix116_26 hinj116_26 hcardT116_26
      (fun i => conj_mem_of_fixedPoints _ _ (T116_26 i) (hfix116_26 i) _)
      ⟨116, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T116_26_2 Q2.hfix116_26_2 Q2.hinj116_26_2
      Q2.hcardT116_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_26_2 i) (Q2.hfix116_26_2 i) _)
      colCert_116_26_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T116_26
      hfix116_26 hinj116_26 hcardT116_26
      (fun i => conj_mem_of_fixedPoints _ _ (T116_26 i) (hfix116_26 i) _)
      ⟨116, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T116_26_2 Q2.hfix116_26_2 Q2.hinj116_26_2
      Q2.hcardT116_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_26_2 i) (Q2.hfix116_26_2 i) _)
      colCert_116_26_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T116_26
      hfix116_26 hinj116_26 hcardT116_26
      (fun i => conj_mem_of_fixedPoints _ _ (T116_26 i) (hfix116_26 i) _)
      ⟨116, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T116_26_2 Q2.hfix116_26_2 Q2.hinj116_26_2
      Q2.hcardT116_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_26_2 i) (Q2.hfix116_26_2 i) _)
      colCert_116_26_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T116_26
      hfix116_26 hinj116_26 hcardT116_26
      (fun i => conj_mem_of_fixedPoints _ _ (T116_26 i) (hfix116_26 i) _)
      ⟨116, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T116_26_2 Q2.hfix116_26_2 Q2.hinj116_26_2
      Q2.hcardT116_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_26_2 i) (Q2.hfix116_26_2 i) _)
      colCert_116_26_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T116_26
      hfix116_26 hinj116_26 hcardT116_26
      (fun i => conj_mem_of_fixedPoints _ _ (T116_26 i) (hfix116_26 i) _)
      ⟨116, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T116_26_2 Q2.hfix116_26_2 Q2.hinj116_26_2
      Q2.hcardT116_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_26_2 i) (Q2.hfix116_26_2 i) _)
      colCert_116_26_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T116_26
      hfix116_26 hinj116_26 hcardT116_26
      (fun i => conj_mem_of_fixedPoints _ _ (T116_26 i) (hfix116_26 i) _)
      ⟨116, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T116_26_2 Q2.hfix116_26_2 Q2.hinj116_26_2
      Q2.hcardT116_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_26_2 i) (Q2.hfix116_26_2 i) _)
      colCert_116_26_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T116_26
      hfix116_26 hinj116_26 hcardT116_26
      (fun i => conj_mem_of_fixedPoints _ _ (T116_26 i) (hfix116_26 i) _)
      ⟨116, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T116_26_2 Q2.hfix116_26_2 Q2.hinj116_26_2
      Q2.hcardT116_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_26_2 i) (Q2.hfix116_26_2 i) _)
      colCert_116_26_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T116_26
      hfix116_26 hinj116_26 hcardT116_26
      (fun i => conj_mem_of_fixedPoints _ _ (T116_26 i) (hfix116_26 i) _)
      ⟨116, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T116_26_2 Q2.hfix116_26_2 Q2.hinj116_26_2
      Q2.hcardT116_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_26_2 i) (Q2.hfix116_26_2 i) _)
      colCert_116_26_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T116_27
      hfix116_27 hinj116_27 hcardT116_27
      (fun i => conj_mem_of_fixedPoints _ _ (T116_27 i) (hfix116_27 i) _)
      ⟨116, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T116_27_2 Q2.hfix116_27_2 Q2.hinj116_27_2
      Q2.hcardT116_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_27_2 i) (Q2.hfix116_27_2 i) _)
      colCert_116_27_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T116_27
      hfix116_27 hinj116_27 hcardT116_27
      (fun i => conj_mem_of_fixedPoints _ _ (T116_27 i) (hfix116_27 i) _)
      ⟨116, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T116_27_2 Q2.hfix116_27_2 Q2.hinj116_27_2
      Q2.hcardT116_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_27_2 i) (Q2.hfix116_27_2 i) _)
      colCert_116_27_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T116_27
      hfix116_27 hinj116_27 hcardT116_27
      (fun i => conj_mem_of_fixedPoints _ _ (T116_27 i) (hfix116_27 i) _)
      ⟨116, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T116_27_2 Q2.hfix116_27_2 Q2.hinj116_27_2
      Q2.hcardT116_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_27_2 i) (Q2.hfix116_27_2 i) _)
      colCert_116_27_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T116_27
      hfix116_27 hinj116_27 hcardT116_27
      (fun i => conj_mem_of_fixedPoints _ _ (T116_27 i) (hfix116_27 i) _)
      ⟨116, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T116_27_2 Q2.hfix116_27_2 Q2.hinj116_27_2
      Q2.hcardT116_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_27_2 i) (Q2.hfix116_27_2 i) _)
      colCert_116_27_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T116_27
      hfix116_27 hinj116_27 hcardT116_27
      (fun i => conj_mem_of_fixedPoints _ _ (T116_27 i) (hfix116_27 i) _)
      ⟨116, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T116_27_2 Q2.hfix116_27_2 Q2.hinj116_27_2
      Q2.hcardT116_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_27_2 i) (Q2.hfix116_27_2 i) _)
      colCert_116_27_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T116_27
      hfix116_27 hinj116_27 hcardT116_27
      (fun i => conj_mem_of_fixedPoints _ _ (T116_27 i) (hfix116_27 i) _)
      ⟨116, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T116_27_2 Q2.hfix116_27_2 Q2.hinj116_27_2
      Q2.hcardT116_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_27_2 i) (Q2.hfix116_27_2 i) _)
      colCert_116_27_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T116_27
      hfix116_27 hinj116_27 hcardT116_27
      (fun i => conj_mem_of_fixedPoints _ _ (T116_27 i) (hfix116_27 i) _)
      ⟨116, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T116_27_2 Q2.hfix116_27_2 Q2.hinj116_27_2
      Q2.hcardT116_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_27_2 i) (Q2.hfix116_27_2 i) _)
      colCert_116_27_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T116_27
      hfix116_27 hinj116_27 hcardT116_27
      (fun i => conj_mem_of_fixedPoints _ _ (T116_27 i) (hfix116_27 i) _)
      ⟨116, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T116_27_2 Q2.hfix116_27_2 Q2.hinj116_27_2
      Q2.hcardT116_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_27_2 i) (Q2.hfix116_27_2 i) _)
      colCert_116_27_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T116_27
      hfix116_27 hinj116_27 hcardT116_27
      (fun i => conj_mem_of_fixedPoints _ _ (T116_27 i) (hfix116_27 i) _)
      ⟨116, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T116_27_2 Q2.hfix116_27_2 Q2.hinj116_27_2
      Q2.hcardT116_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_27_2 i) (Q2.hfix116_27_2 i) _)
      colCert_116_27_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T116_28
      hfix116_28 hinj116_28 hcardT116_28
      (fun i => conj_mem_of_fixedPoints _ _ (T116_28 i) (hfix116_28 i) _)
      ⟨116, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T116_28_2 Q2.hfix116_28_2 Q2.hinj116_28_2
      Q2.hcardT116_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_28_2 i) (Q2.hfix116_28_2 i) _)
      colCert_116_28_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T116_28
      hfix116_28 hinj116_28 hcardT116_28
      (fun i => conj_mem_of_fixedPoints _ _ (T116_28 i) (hfix116_28 i) _)
      ⟨116, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T116_28_2 Q2.hfix116_28_2 Q2.hinj116_28_2
      Q2.hcardT116_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_28_2 i) (Q2.hfix116_28_2 i) _)
      colCert_116_28_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T116_28
      hfix116_28 hinj116_28 hcardT116_28
      (fun i => conj_mem_of_fixedPoints _ _ (T116_28 i) (hfix116_28 i) _)
      ⟨116, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T116_28_2 Q2.hfix116_28_2 Q2.hinj116_28_2
      Q2.hcardT116_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_28_2 i) (Q2.hfix116_28_2 i) _)
      colCert_116_28_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T116_28
      hfix116_28 hinj116_28 hcardT116_28
      (fun i => conj_mem_of_fixedPoints _ _ (T116_28 i) (hfix116_28 i) _)
      ⟨116, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T116_28_2 Q2.hfix116_28_2 Q2.hinj116_28_2
      Q2.hcardT116_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_28_2 i) (Q2.hfix116_28_2 i) _)
      colCert_116_28_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T116_28
      hfix116_28 hinj116_28 hcardT116_28
      (fun i => conj_mem_of_fixedPoints _ _ (T116_28 i) (hfix116_28 i) _)
      ⟨116, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T116_28_2 Q2.hfix116_28_2 Q2.hinj116_28_2
      Q2.hcardT116_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_28_2 i) (Q2.hfix116_28_2 i) _)
      colCert_116_28_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T116_28
      hfix116_28 hinj116_28 hcardT116_28
      (fun i => conj_mem_of_fixedPoints _ _ (T116_28 i) (hfix116_28 i) _)
      ⟨116, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T116_28_2 Q2.hfix116_28_2 Q2.hinj116_28_2
      Q2.hcardT116_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_28_2 i) (Q2.hfix116_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T116_28 = colFn colCertDiv_116_28_5.D1 (m := 5) from colCertDiv_116_28_5.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 5 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T116_28_2 = colFn colCertDiv_116_28_5.D2 (m := 5) from colCertDiv_116_28_5.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_28_5_match


theorem leaf_116_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T116_28
      hfix116_28 hinj116_28 hcardT116_28
      (fun i => conj_mem_of_fixedPoints _ _ (T116_28 i) (hfix116_28 i) _)
      ⟨116, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T116_28_2 Q2.hfix116_28_2 Q2.hinj116_28_2
      Q2.hcardT116_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_28_2 i) (Q2.hfix116_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T116_28 = colFn colCertDiv_116_28_10.D1 (m := 5) from colCertDiv_116_28_10.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 10 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T116_28_2 = colFn colCertDiv_116_28_10.D2 (m := 5) from colCertDiv_116_28_10.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_28_10_match


theorem leaf_116_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T116_28
      hfix116_28 hinj116_28 hcardT116_28
      (fun i => conj_mem_of_fixedPoints _ _ (T116_28 i) (hfix116_28 i) _)
      ⟨116, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T116_28_2 Q2.hfix116_28_2 Q2.hinj116_28_2
      Q2.hcardT116_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_28_2 i) (Q2.hfix116_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T116_28 = colFn colCertDiv_116_28_15.D1 (m := 5) from colCertDiv_116_28_15.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 15 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T116_28_2 = colFn colCertDiv_116_28_15.D2 (m := 5) from colCertDiv_116_28_15.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_28_15_match


theorem leaf_116_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T116_28
      hfix116_28 hinj116_28 hcardT116_28
      (fun i => conj_mem_of_fixedPoints _ _ (T116_28 i) (hfix116_28 i) _)
      ⟨116, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T116_28_2 Q2.hfix116_28_2 Q2.hinj116_28_2
      Q2.hcardT116_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_28_2 i) (Q2.hfix116_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T116_28 = colFn colCertDiv_116_28_20.D1 (m := 5) from colCertDiv_116_28_20.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 20 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T116_28_2 = colFn colCertDiv_116_28_20.D2 (m := 5) from colCertDiv_116_28_20.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_28_20_match


theorem leaf_116_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T116_33
      hfix116_33 hinj116_33 hcardT116_33
      (fun i => conj_mem_of_fixedPoints _ _ (T116_33 i) (hfix116_33 i) _)
      ⟨116, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T116_33_2 Q2.hfix116_33_2 Q2.hinj116_33_2
      Q2.hcardT116_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_33_2 i) (Q2.hfix116_33_2 i) _)
      colCert_116_33_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T116_33
      hfix116_33 hinj116_33 hcardT116_33
      (fun i => conj_mem_of_fixedPoints _ _ (T116_33 i) (hfix116_33 i) _)
      ⟨116, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T116_33_2 Q2.hfix116_33_2 Q2.hinj116_33_2
      Q2.hcardT116_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_33_2 i) (Q2.hfix116_33_2 i) _)
      colCert_116_33_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T116_33
      hfix116_33 hinj116_33 hcardT116_33
      (fun i => conj_mem_of_fixedPoints _ _ (T116_33 i) (hfix116_33 i) _)
      ⟨116, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T116_33_2 Q2.hfix116_33_2 Q2.hinj116_33_2
      Q2.hcardT116_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_33_2 i) (Q2.hfix116_33_2 i) _)
      colCert_116_33_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T116_33
      hfix116_33 hinj116_33 hcardT116_33
      (fun i => conj_mem_of_fixedPoints _ _ (T116_33 i) (hfix116_33 i) _)
      ⟨116, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T116_33_2 Q2.hfix116_33_2 Q2.hinj116_33_2
      Q2.hcardT116_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_33_2 i) (Q2.hfix116_33_2 i) _)
      colCert_116_33_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T116_33
      hfix116_33 hinj116_33 hcardT116_33
      (fun i => conj_mem_of_fixedPoints _ _ (T116_33 i) (hfix116_33 i) _)
      ⟨116, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T116_33_2 Q2.hfix116_33_2 Q2.hinj116_33_2
      Q2.hcardT116_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_33_2 i) (Q2.hfix116_33_2 i) _)
      colCert_116_33_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T116_33
      hfix116_33 hinj116_33 hcardT116_33
      (fun i => conj_mem_of_fixedPoints _ _ (T116_33 i) (hfix116_33 i) _)
      ⟨116, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T116_33_2 Q2.hfix116_33_2 Q2.hinj116_33_2
      Q2.hcardT116_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_33_2 i) (Q2.hfix116_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T116_33 = colFn colCertDiv_116_33_5.D1 (m := 5) from colCertDiv_116_33_5.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T116_33_2 = colFn colCertDiv_116_33_5.D2 (m := 5) from colCertDiv_116_33_5.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_33_5_match


theorem leaf_116_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T116_33
      hfix116_33 hinj116_33 hcardT116_33
      (fun i => conj_mem_of_fixedPoints _ _ (T116_33 i) (hfix116_33 i) _)
      ⟨116, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T116_33_2 Q2.hfix116_33_2 Q2.hinj116_33_2
      Q2.hcardT116_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_33_2 i) (Q2.hfix116_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T116_33 = colFn colCertDiv_116_33_10.D1 (m := 5) from colCertDiv_116_33_10.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T116_33_2 = colFn colCertDiv_116_33_10.D2 (m := 5) from colCertDiv_116_33_10.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_33_10_match


theorem leaf_116_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T116_33
      hfix116_33 hinj116_33 hcardT116_33
      (fun i => conj_mem_of_fixedPoints _ _ (T116_33 i) (hfix116_33 i) _)
      ⟨116, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T116_33_2 Q2.hfix116_33_2 Q2.hinj116_33_2
      Q2.hcardT116_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_33_2 i) (Q2.hfix116_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T116_33 = colFn colCertDiv_116_33_15.D1 (m := 5) from colCertDiv_116_33_15.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T116_33_2 = colFn colCertDiv_116_33_15.D2 (m := 5) from colCertDiv_116_33_15.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_33_15_match


theorem leaf_116_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T116_33
      hfix116_33 hinj116_33 hcardT116_33
      (fun i => conj_mem_of_fixedPoints _ _ (T116_33 i) (hfix116_33 i) _)
      ⟨116, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T116_33_2 Q2.hfix116_33_2 Q2.hinj116_33_2
      Q2.hcardT116_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_33_2 i) (Q2.hfix116_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T116_33 = colFn colCertDiv_116_33_20.D1 (m := 5) from colCertDiv_116_33_20.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T116_33_2 = colFn colCertDiv_116_33_20.D2 (m := 5) from colCertDiv_116_33_20.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_33_20_match


theorem leaf_116_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T116_38
      hfix116_38 hinj116_38 hcardT116_38
      (fun i => conj_mem_of_fixedPoints _ _ (T116_38 i) (hfix116_38 i) _)
      ⟨116, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T116_38_2 Q2.hfix116_38_2 Q2.hinj116_38_2
      Q2.hcardT116_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_38_2 i) (Q2.hfix116_38_2 i) _)
      colCert_116_38_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T116_38
      hfix116_38 hinj116_38 hcardT116_38
      (fun i => conj_mem_of_fixedPoints _ _ (T116_38 i) (hfix116_38 i) _)
      ⟨116, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T116_38_2 Q2.hfix116_38_2 Q2.hinj116_38_2
      Q2.hcardT116_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_38_2 i) (Q2.hfix116_38_2 i) _)
      colCert_116_38_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T116_38
      hfix116_38 hinj116_38 hcardT116_38
      (fun i => conj_mem_of_fixedPoints _ _ (T116_38 i) (hfix116_38 i) _)
      ⟨116, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T116_38_2 Q2.hfix116_38_2 Q2.hinj116_38_2
      Q2.hcardT116_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_38_2 i) (Q2.hfix116_38_2 i) _)
      colCert_116_38_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T116_38
      hfix116_38 hinj116_38 hcardT116_38
      (fun i => conj_mem_of_fixedPoints _ _ (T116_38 i) (hfix116_38 i) _)
      ⟨116, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T116_38_2 Q2.hfix116_38_2 Q2.hinj116_38_2
      Q2.hcardT116_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_38_2 i) (Q2.hfix116_38_2 i) _)
      colCert_116_38_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T116_38
      hfix116_38 hinj116_38 hcardT116_38
      (fun i => conj_mem_of_fixedPoints _ _ (T116_38 i) (hfix116_38 i) _)
      ⟨116, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T116_38_2 Q2.hfix116_38_2 Q2.hinj116_38_2
      Q2.hcardT116_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_38_2 i) (Q2.hfix116_38_2 i) _)
      colCert_116_38_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T116_38
      hfix116_38 hinj116_38 hcardT116_38
      (fun i => conj_mem_of_fixedPoints _ _ (T116_38 i) (hfix116_38 i) _)
      ⟨116, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T116_38_2 Q2.hfix116_38_2 Q2.hinj116_38_2
      Q2.hcardT116_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_38_2 i) (Q2.hfix116_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T116_38 = colFn colCertDiv_116_38_5.D1 (m := 5) from colCertDiv_116_38_5.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T116_38_2 = colFn colCertDiv_116_38_5.D2 (m := 5) from colCertDiv_116_38_5.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_38_5_match


theorem leaf_116_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T116_38
      hfix116_38 hinj116_38 hcardT116_38
      (fun i => conj_mem_of_fixedPoints _ _ (T116_38 i) (hfix116_38 i) _)
      ⟨116, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T116_38_2 Q2.hfix116_38_2 Q2.hinj116_38_2
      Q2.hcardT116_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_38_2 i) (Q2.hfix116_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T116_38 = colFn colCertDiv_116_38_10.D1 (m := 5) from colCertDiv_116_38_10.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T116_38_2 = colFn colCertDiv_116_38_10.D2 (m := 5) from colCertDiv_116_38_10.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_38_10_match


theorem leaf_116_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T116_38
      hfix116_38 hinj116_38 hcardT116_38
      (fun i => conj_mem_of_fixedPoints _ _ (T116_38 i) (hfix116_38 i) _)
      ⟨116, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T116_38_2 Q2.hfix116_38_2 Q2.hinj116_38_2
      Q2.hcardT116_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_38_2 i) (Q2.hfix116_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T116_38 = colFn colCertDiv_116_38_15.D1 (m := 5) from colCertDiv_116_38_15.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T116_38_2 = colFn colCertDiv_116_38_15.D2 (m := 5) from colCertDiv_116_38_15.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_38_15_match


theorem leaf_116_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T116_38
      hfix116_38 hinj116_38 hcardT116_38
      (fun i => conj_mem_of_fixedPoints _ _ (T116_38 i) (hfix116_38 i) _)
      ⟨116, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T116_38_2 Q2.hfix116_38_2 Q2.hinj116_38_2
      Q2.hcardT116_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_38_2 i) (Q2.hfix116_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T116_38 = colFn colCertDiv_116_38_20.D1 (m := 5) from colCertDiv_116_38_20.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T116_38_2 = colFn colCertDiv_116_38_20.D2 (m := 5) from colCertDiv_116_38_20.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_38_20_match


theorem leaf_116_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T116_43
      hfix116_43 hinj116_43 hcardT116_43
      (fun i => conj_mem_of_fixedPoints _ _ (T116_43 i) (hfix116_43 i) _)
      ⟨116, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T116_43_2 Q2.hfix116_43_2 Q2.hinj116_43_2
      Q2.hcardT116_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_43_2 i) (Q2.hfix116_43_2 i) _)
      colCert_116_43_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T116_43
      hfix116_43 hinj116_43 hcardT116_43
      (fun i => conj_mem_of_fixedPoints _ _ (T116_43 i) (hfix116_43 i) _)
      ⟨116, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T116_43_2 Q2.hfix116_43_2 Q2.hinj116_43_2
      Q2.hcardT116_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_43_2 i) (Q2.hfix116_43_2 i) _)
      colCert_116_43_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T116_43
      hfix116_43 hinj116_43 hcardT116_43
      (fun i => conj_mem_of_fixedPoints _ _ (T116_43 i) (hfix116_43 i) _)
      ⟨116, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T116_43_2 Q2.hfix116_43_2 Q2.hinj116_43_2
      Q2.hcardT116_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_43_2 i) (Q2.hfix116_43_2 i) _)
      colCert_116_43_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T116_43
      hfix116_43 hinj116_43 hcardT116_43
      (fun i => conj_mem_of_fixedPoints _ _ (T116_43 i) (hfix116_43 i) _)
      ⟨116, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T116_43_2 Q2.hfix116_43_2 Q2.hinj116_43_2
      Q2.hcardT116_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_43_2 i) (Q2.hfix116_43_2 i) _)
      colCert_116_43_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T116_43
      hfix116_43 hinj116_43 hcardT116_43
      (fun i => conj_mem_of_fixedPoints _ _ (T116_43 i) (hfix116_43 i) _)
      ⟨116, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T116_43_2 Q2.hfix116_43_2 Q2.hinj116_43_2
      Q2.hcardT116_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_43_2 i) (Q2.hfix116_43_2 i) _)
      colCert_116_43_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T116_43
      hfix116_43 hinj116_43 hcardT116_43
      (fun i => conj_mem_of_fixedPoints _ _ (T116_43 i) (hfix116_43 i) _)
      ⟨116, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T116_43_2 Q2.hfix116_43_2 Q2.hinj116_43_2
      Q2.hcardT116_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_43_2 i) (Q2.hfix116_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T116_43 = colFn colCertDiv_116_43_5.D1 (m := 5) from colCertDiv_116_43_5.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T116_43_2 = colFn colCertDiv_116_43_5.D2 (m := 5) from colCertDiv_116_43_5.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_43_5_match


theorem leaf_116_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T116_43
      hfix116_43 hinj116_43 hcardT116_43
      (fun i => conj_mem_of_fixedPoints _ _ (T116_43 i) (hfix116_43 i) _)
      ⟨116, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T116_43_2 Q2.hfix116_43_2 Q2.hinj116_43_2
      Q2.hcardT116_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_43_2 i) (Q2.hfix116_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T116_43 = colFn colCertDiv_116_43_10.D1 (m := 5) from colCertDiv_116_43_10.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T116_43_2 = colFn colCertDiv_116_43_10.D2 (m := 5) from colCertDiv_116_43_10.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_43_10_match


theorem leaf_116_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T116_43
      hfix116_43 hinj116_43 hcardT116_43
      (fun i => conj_mem_of_fixedPoints _ _ (T116_43 i) (hfix116_43 i) _)
      ⟨116, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T116_43_2 Q2.hfix116_43_2 Q2.hinj116_43_2
      Q2.hcardT116_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_43_2 i) (Q2.hfix116_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T116_43 = colFn colCertDiv_116_43_15.D1 (m := 5) from colCertDiv_116_43_15.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T116_43_2 = colFn colCertDiv_116_43_15.D2 (m := 5) from colCertDiv_116_43_15.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_43_15_match


theorem leaf_116_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T116_43
      hfix116_43 hinj116_43 hcardT116_43
      (fun i => conj_mem_of_fixedPoints _ _ (T116_43 i) (hfix116_43 i) _)
      ⟨116, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T116_43_2 Q2.hfix116_43_2 Q2.hinj116_43_2
      Q2.hcardT116_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_43_2 i) (Q2.hfix116_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T116_43 = colFn colCertDiv_116_43_20.D1 (m := 5) from colCertDiv_116_43_20.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T116_43_2 = colFn colCertDiv_116_43_20.D2 (m := 5) from colCertDiv_116_43_20.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_43_20_match


theorem leaf_116_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T116_48
      hfix116_48 hinj116_48 hcardT116_48
      (fun i => conj_mem_of_fixedPoints _ _ (T116_48 i) (hfix116_48 i) _)
      ⟨116, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T116_48_2 Q2.hfix116_48_2 Q2.hinj116_48_2
      Q2.hcardT116_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_48_2 i) (Q2.hfix116_48_2 i) _)
      colCert_116_48_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T116_48
      hfix116_48 hinj116_48 hcardT116_48
      (fun i => conj_mem_of_fixedPoints _ _ (T116_48 i) (hfix116_48 i) _)
      ⟨116, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T116_48_2 Q2.hfix116_48_2 Q2.hinj116_48_2
      Q2.hcardT116_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_48_2 i) (Q2.hfix116_48_2 i) _)
      colCert_116_48_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T116_48
      hfix116_48 hinj116_48 hcardT116_48
      (fun i => conj_mem_of_fixedPoints _ _ (T116_48 i) (hfix116_48 i) _)
      ⟨116, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T116_48_2 Q2.hfix116_48_2 Q2.hinj116_48_2
      Q2.hcardT116_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_48_2 i) (Q2.hfix116_48_2 i) _)
      colCert_116_48_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T116_48
      hfix116_48 hinj116_48 hcardT116_48
      (fun i => conj_mem_of_fixedPoints _ _ (T116_48 i) (hfix116_48 i) _)
      ⟨116, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T116_48_2 Q2.hfix116_48_2 Q2.hinj116_48_2
      Q2.hcardT116_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_48_2 i) (Q2.hfix116_48_2 i) _)
      colCert_116_48_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T116_48
      hfix116_48 hinj116_48 hcardT116_48
      (fun i => conj_mem_of_fixedPoints _ _ (T116_48 i) (hfix116_48 i) _)
      ⟨116, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T116_48_2 Q2.hfix116_48_2 Q2.hinj116_48_2
      Q2.hcardT116_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_48_2 i) (Q2.hfix116_48_2 i) _)
      colCert_116_48_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T116_48
      hfix116_48 hinj116_48 hcardT116_48
      (fun i => conj_mem_of_fixedPoints _ _ (T116_48 i) (hfix116_48 i) _)
      ⟨116, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T116_48_2 Q2.hfix116_48_2 Q2.hinj116_48_2
      Q2.hcardT116_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_48_2 i) (Q2.hfix116_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T116_48 = colFn colCertDiv_116_48_5.D1 (m := 5) from colCertDiv_116_48_5.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T116_48_2 = colFn colCertDiv_116_48_5.D2 (m := 5) from colCertDiv_116_48_5.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_48_5_match


theorem leaf_116_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T116_48
      hfix116_48 hinj116_48 hcardT116_48
      (fun i => conj_mem_of_fixedPoints _ _ (T116_48 i) (hfix116_48 i) _)
      ⟨116, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T116_48_2 Q2.hfix116_48_2 Q2.hinj116_48_2
      Q2.hcardT116_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_48_2 i) (Q2.hfix116_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T116_48 = colFn colCertDiv_116_48_10.D1 (m := 5) from colCertDiv_116_48_10.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T116_48_2 = colFn colCertDiv_116_48_10.D2 (m := 5) from colCertDiv_116_48_10.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_48_10_match


theorem leaf_116_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T116_48
      hfix116_48 hinj116_48 hcardT116_48
      (fun i => conj_mem_of_fixedPoints _ _ (T116_48 i) (hfix116_48 i) _)
      ⟨116, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T116_48_2 Q2.hfix116_48_2 Q2.hinj116_48_2
      Q2.hcardT116_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_48_2 i) (Q2.hfix116_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T116_48 = colFn colCertDiv_116_48_15.D1 (m := 5) from colCertDiv_116_48_15.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T116_48_2 = colFn colCertDiv_116_48_15.D2 (m := 5) from colCertDiv_116_48_15.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_48_15_match


theorem leaf_116_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T116_48
      hfix116_48 hinj116_48 hcardT116_48
      (fun i => conj_mem_of_fixedPoints _ _ (T116_48 i) (hfix116_48 i) _)
      ⟨116, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T116_48_2 Q2.hfix116_48_2 Q2.hinj116_48_2
      Q2.hcardT116_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_48_2 i) (Q2.hfix116_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T116_48 = colFn colCertDiv_116_48_20.D1 (m := 5) from colCertDiv_116_48_20.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T116_48_2 = colFn colCertDiv_116_48_20.D2 (m := 5) from colCertDiv_116_48_20.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_48_20_match


theorem leaf_116_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T116_53
      hfix116_53 hinj116_53 hcardT116_53
      (fun i => conj_mem_of_fixedPoints _ _ (T116_53 i) (hfix116_53 i) _)
      ⟨116, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T116_53_2 Q2.hfix116_53_2 Q2.hinj116_53_2
      Q2.hcardT116_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_53_2 i) (Q2.hfix116_53_2 i) _)
      colCert_116_53_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T116_53
      hfix116_53 hinj116_53 hcardT116_53
      (fun i => conj_mem_of_fixedPoints _ _ (T116_53 i) (hfix116_53 i) _)
      ⟨116, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T116_53_2 Q2.hfix116_53_2 Q2.hinj116_53_2
      Q2.hcardT116_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_53_2 i) (Q2.hfix116_53_2 i) _)
      colCert_116_53_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T116_53
      hfix116_53 hinj116_53 hcardT116_53
      (fun i => conj_mem_of_fixedPoints _ _ (T116_53 i) (hfix116_53 i) _)
      ⟨116, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T116_53_2 Q2.hfix116_53_2 Q2.hinj116_53_2
      Q2.hcardT116_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_53_2 i) (Q2.hfix116_53_2 i) _)
      colCert_116_53_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T116_53
      hfix116_53 hinj116_53 hcardT116_53
      (fun i => conj_mem_of_fixedPoints _ _ (T116_53 i) (hfix116_53 i) _)
      ⟨116, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T116_53_2 Q2.hfix116_53_2 Q2.hinj116_53_2
      Q2.hcardT116_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_53_2 i) (Q2.hfix116_53_2 i) _)
      colCert_116_53_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T116_53
      hfix116_53 hinj116_53 hcardT116_53
      (fun i => conj_mem_of_fixedPoints _ _ (T116_53 i) (hfix116_53 i) _)
      ⟨116, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T116_53_2 Q2.hfix116_53_2 Q2.hinj116_53_2
      Q2.hcardT116_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_53_2 i) (Q2.hfix116_53_2 i) _)
      colCert_116_53_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T116_53
      hfix116_53 hinj116_53 hcardT116_53
      (fun i => conj_mem_of_fixedPoints _ _ (T116_53 i) (hfix116_53 i) _)
      ⟨116, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T116_53_2 Q2.hfix116_53_2 Q2.hinj116_53_2
      Q2.hcardT116_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_53_2 i) (Q2.hfix116_53_2 i) _)
      colCert_116_53_5.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T116_53
      hfix116_53 hinj116_53 hcardT116_53
      (fun i => conj_mem_of_fixedPoints _ _ (T116_53 i) (hfix116_53 i) _)
      ⟨116, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T116_53_2 Q2.hfix116_53_2 Q2.hinj116_53_2
      Q2.hcardT116_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_53_2 i) (Q2.hfix116_53_2 i) _)
      colCert_116_53_10.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T116_53
      hfix116_53 hinj116_53 hcardT116_53
      (fun i => conj_mem_of_fixedPoints _ _ (T116_53 i) (hfix116_53 i) _)
      ⟨116, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T116_53_2 Q2.hfix116_53_2 Q2.hinj116_53_2
      Q2.hcardT116_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_53_2 i) (Q2.hfix116_53_2 i) _)
      colCert_116_53_15.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T116_53
      hfix116_53 hinj116_53 hcardT116_53
      (fun i => conj_mem_of_fixedPoints _ _ (T116_53 i) (hfix116_53 i) _)
      ⟨116, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T116_53_2 Q2.hfix116_53_2 Q2.hinj116_53_2
      Q2.hcardT116_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_53_2 i) (Q2.hfix116_53_2 i) _)
      colCert_116_53_20.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_55_0 (hp : 0 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 0 (transLenTr ⟨55, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 0 (transLenTr ⟨55, by decide⟩ 0 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 0 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      colCert_116_55_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_55_1 (hp : 1 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 1 (transLenTr ⟨55, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 1 (transLenTr ⟨55, by decide⟩ 1 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 1 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      colCert_116_55_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_55_2 (hp : 2 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 2 (transLenTr ⟨55, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 2 (transLenTr ⟨55, by decide⟩ 2 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 2 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      colCert_116_55_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_55_3 (hp : 3 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 3 (transLenTr ⟨55, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 3 (transLenTr ⟨55, by decide⟩ 3 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 3 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      colCert_116_55_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_55_4 (hp : 4 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 4 (transLenTr ⟨55, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 4 (transLenTr ⟨55, by decide⟩ 4 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 4 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      colCert_116_55_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_55_5 (hp : 5 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 5 (transLenTr ⟨55, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 5 (transLenTr ⟨55, by decide⟩ 5 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 5 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 5 (transLenTr ⟨55, by decide⟩ 5 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_5.D1 (m := 5) from colCertDiv_116_55_5.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 5 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_5.D2 (m := 5) from colCertDiv_116_55_5.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_5_match


theorem leaf_116_55_6 (hp : 6 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 6 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 6 (transLenTr ⟨55, by decide⟩ 6 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 6 (transLenTr ⟨55, by decide⟩ 6 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 6 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 6 (transLenTr ⟨55, by decide⟩ 6 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_6.D1 (m := 5) from colCertDiv_116_55_6.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 6 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_6.D2 (m := 5) from colCertDiv_116_55_6.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_6_match


theorem leaf_116_55_7 (hp : 7 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 7 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 7 (transLenTr ⟨55, by decide⟩ 7 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 7 (transLenTr ⟨55, by decide⟩ 7 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 7 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 7 (transLenTr ⟨55, by decide⟩ 7 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_7.D1 (m := 5) from colCertDiv_116_55_7.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 7 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_7.D2 (m := 5) from colCertDiv_116_55_7.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_7_match


theorem leaf_116_55_8 (hp : 8 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 8 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 8 (transLenTr ⟨55, by decide⟩ 8 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 8 (transLenTr ⟨55, by decide⟩ 8 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 8 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 8 (transLenTr ⟨55, by decide⟩ 8 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_8.D1 (m := 5) from colCertDiv_116_55_8.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 8 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_8.D2 (m := 5) from colCertDiv_116_55_8.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_8_match


theorem leaf_116_55_9 (hp : 9 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 9 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 9 (transLenTr ⟨55, by decide⟩ 9 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 9 (transLenTr ⟨55, by decide⟩ 9 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 9 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 9 (transLenTr ⟨55, by decide⟩ 9 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_9.D1 (m := 5) from colCertDiv_116_55_9.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 9 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_9.D2 (m := 5) from colCertDiv_116_55_9.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_9_match


theorem leaf_116_55_10 (hp : 10 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 10 (transLenTr ⟨55, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 10 (transLenTr ⟨55, by decide⟩ 10 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 10 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 10 (transLenTr ⟨55, by decide⟩ 10 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_10.D1 (m := 5) from colCertDiv_116_55_10.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 10 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_10.D2 (m := 5) from colCertDiv_116_55_10.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_10_match


theorem leaf_116_55_11 (hp : 11 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 11 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 11 (transLenTr ⟨55, by decide⟩ 11 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 11 (transLenTr ⟨55, by decide⟩ 11 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 11 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 11 (transLenTr ⟨55, by decide⟩ 11 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_11.D1 (m := 5) from colCertDiv_116_55_11.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 11 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_11.D2 (m := 5) from colCertDiv_116_55_11.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_11_match


theorem leaf_116_55_12 (hp : 12 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 12 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 12 (transLenTr ⟨55, by decide⟩ 12 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 12 (transLenTr ⟨55, by decide⟩ 12 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 12 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 12 (transLenTr ⟨55, by decide⟩ 12 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_12.D1 (m := 5) from colCertDiv_116_55_12.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 12 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_12.D2 (m := 5) from colCertDiv_116_55_12.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_12_match


theorem leaf_116_55_13 (hp : 13 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 13 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 13 (transLenTr ⟨55, by decide⟩ 13 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 13 (transLenTr ⟨55, by decide⟩ 13 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 13 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 13 (transLenTr ⟨55, by decide⟩ 13 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_13.D1 (m := 5) from colCertDiv_116_55_13.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 13 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_13.D2 (m := 5) from colCertDiv_116_55_13.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_13_match


theorem leaf_116_55_14 (hp : 14 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 14 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 14 (transLenTr ⟨55, by decide⟩ 14 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 14 (transLenTr ⟨55, by decide⟩ 14 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 14 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 14 (transLenTr ⟨55, by decide⟩ 14 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_14.D1 (m := 5) from colCertDiv_116_55_14.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 14 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_14.D2 (m := 5) from colCertDiv_116_55_14.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_14_match


theorem leaf_116_55_15 (hp : 15 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 15 (transLenTr ⟨55, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 15 (transLenTr ⟨55, by decide⟩ 15 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 15 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 15 (transLenTr ⟨55, by decide⟩ 15 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_15.D1 (m := 5) from colCertDiv_116_55_15.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 15 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_15.D2 (m := 5) from colCertDiv_116_55_15.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_15_match


theorem leaf_116_55_16 (hp : 16 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 16 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 16 (transLenTr ⟨55, by decide⟩ 16 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 16 (transLenTr ⟨55, by decide⟩ 16 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 16 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 16 (transLenTr ⟨55, by decide⟩ 16 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_16.D1 (m := 5) from colCertDiv_116_55_16.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 16 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_16.D2 (m := 5) from colCertDiv_116_55_16.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_16_match


theorem leaf_116_55_17 (hp : 17 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 17 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 17 (transLenTr ⟨55, by decide⟩ 17 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 17 (transLenTr ⟨55, by decide⟩ 17 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 17 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 17 (transLenTr ⟨55, by decide⟩ 17 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_17.D1 (m := 5) from colCertDiv_116_55_17.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 17 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_17.D2 (m := 5) from colCertDiv_116_55_17.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_17_match


theorem leaf_116_55_18 (hp : 18 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 18 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 18 (transLenTr ⟨55, by decide⟩ 18 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 18 (transLenTr ⟨55, by decide⟩ 18 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 18 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 18 (transLenTr ⟨55, by decide⟩ 18 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_18.D1 (m := 5) from colCertDiv_116_55_18.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 18 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_18.D2 (m := 5) from colCertDiv_116_55_18.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_18_match


theorem leaf_116_55_19 (hp : 19 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 19 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 19 (transLenTr ⟨55, by decide⟩ 19 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 19 (transLenTr ⟨55, by decide⟩ 19 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 19 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 19 (transLenTr ⟨55, by decide⟩ 19 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_19.D1 (m := 5) from colCertDiv_116_55_19.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 19 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_19.D2 (m := 5) from colCertDiv_116_55_19.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_19_match


theorem leaf_116_55_20 (hp : 20 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 20 (transLenTr ⟨55, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 20 (transLenTr ⟨55, by decide⟩ 20 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 20 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 20 (transLenTr ⟨55, by decide⟩ 20 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_20.D1 (m := 5) from colCertDiv_116_55_20.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 20 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_20.D2 (m := 5) from colCertDiv_116_55_20.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_20_match


theorem leaf_116_55_21 (hp : 21 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 21 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 21 (transLenTr ⟨55, by decide⟩ 21 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 21 (transLenTr ⟨55, by decide⟩ 21 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 21 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 21 (transLenTr ⟨55, by decide⟩ 21 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_21.D1 (m := 5) from colCertDiv_116_55_21.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 21 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_21.D2 (m := 5) from colCertDiv_116_55_21.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_21_match


theorem leaf_116_55_22 (hp : 22 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 22 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 22 (transLenTr ⟨55, by decide⟩ 22 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 22 (transLenTr ⟨55, by decide⟩ 22 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 22 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 22 (transLenTr ⟨55, by decide⟩ 22 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_22.D1 (m := 5) from colCertDiv_116_55_22.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 22 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_22.D2 (m := 5) from colCertDiv_116_55_22.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_22_match


theorem leaf_116_55_23 (hp : 23 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 23 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 23 (transLenTr ⟨55, by decide⟩ 23 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 23 (transLenTr ⟨55, by decide⟩ 23 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 23 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 23 (transLenTr ⟨55, by decide⟩ 23 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_23.D1 (m := 5) from colCertDiv_116_55_23.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 23 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_23.D2 (m := 5) from colCertDiv_116_55_23.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_23_match


theorem leaf_116_55_24 (hp : 24 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 24 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 24 (transLenTr ⟨55, by decide⟩ 24 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 24 (transLenTr ⟨55, by decide⟩ 24 hp)) T116_55
      hfix116_55 hinj116_55 hcardT116_55
      (fun i => conj_mem_of_fixedPoints _ _ (T116_55 i) (hfix116_55 i) _)
      ⟨116, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 24 hp) Q2.T116_55_2 Q2.hfix116_55_2 Q2.hinj116_55_2
      Q2.hcardT116_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_55_2 i) (Q2.hfix116_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 24 (transLenTr ⟨55, by decide⟩ 24 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T116_55 = colFn colCertDiv_116_55_24.D1 (m := 5) from colCertDiv_116_55_24.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 24 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T116_55_2 = colFn colCertDiv_116_55_24.D2 (m := 5) from colCertDiv_116_55_24.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_55_24_match


theorem leaf_116_56_0 (hp : 0 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 0 (transLenTr ⟨56, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 0 (transLenTr ⟨56, by decide⟩ 0 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 0 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      colCert_116_56_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_56_1 (hp : 1 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 1 (transLenTr ⟨56, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 1 (transLenTr ⟨56, by decide⟩ 1 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 1 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      colCert_116_56_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_56_2 (hp : 2 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 2 (transLenTr ⟨56, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 2 (transLenTr ⟨56, by decide⟩ 2 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 2 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      colCert_116_56_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_56_3 (hp : 3 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 3 (transLenTr ⟨56, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 3 (transLenTr ⟨56, by decide⟩ 3 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 3 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      colCert_116_56_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_56_4 (hp : 4 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 4 (transLenTr ⟨56, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 4 (transLenTr ⟨56, by decide⟩ 4 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 4 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      colCert_116_56_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_56_5 (hp : 5 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 5 (transLenTr ⟨56, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 5 (transLenTr ⟨56, by decide⟩ 5 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 5 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 5 (transLenTr ⟨56, by decide⟩ 5 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_5.D1 (m := 5) from colCertDiv_116_56_5.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 5 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_5.D2 (m := 5) from colCertDiv_116_56_5.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_5_match


theorem leaf_116_56_6 (hp : 6 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 6 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 6 (transLenTr ⟨56, by decide⟩ 6 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 6 (transLenTr ⟨56, by decide⟩ 6 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 6 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 6 (transLenTr ⟨56, by decide⟩ 6 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_6.D1 (m := 5) from colCertDiv_116_56_6.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 6 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_6.D2 (m := 5) from colCertDiv_116_56_6.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_6_match


theorem leaf_116_56_7 (hp : 7 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 7 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 7 (transLenTr ⟨56, by decide⟩ 7 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 7 (transLenTr ⟨56, by decide⟩ 7 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 7 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 7 (transLenTr ⟨56, by decide⟩ 7 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_7.D1 (m := 5) from colCertDiv_116_56_7.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 7 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_7.D2 (m := 5) from colCertDiv_116_56_7.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_7_match


theorem leaf_116_56_8 (hp : 8 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 8 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 8 (transLenTr ⟨56, by decide⟩ 8 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 8 (transLenTr ⟨56, by decide⟩ 8 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 8 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 8 (transLenTr ⟨56, by decide⟩ 8 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_8.D1 (m := 5) from colCertDiv_116_56_8.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 8 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_8.D2 (m := 5) from colCertDiv_116_56_8.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_8_match


theorem leaf_116_56_9 (hp : 9 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 9 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 9 (transLenTr ⟨56, by decide⟩ 9 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 9 (transLenTr ⟨56, by decide⟩ 9 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 9 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 9 (transLenTr ⟨56, by decide⟩ 9 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_9.D1 (m := 5) from colCertDiv_116_56_9.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 9 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_9.D2 (m := 5) from colCertDiv_116_56_9.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_9_match


theorem leaf_116_56_10 (hp : 10 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 10 (transLenTr ⟨56, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 10 (transLenTr ⟨56, by decide⟩ 10 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 10 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 10 (transLenTr ⟨56, by decide⟩ 10 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_10.D1 (m := 5) from colCertDiv_116_56_10.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 10 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_10.D2 (m := 5) from colCertDiv_116_56_10.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_10_match


theorem leaf_116_56_11 (hp : 11 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 11 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 11 (transLenTr ⟨56, by decide⟩ 11 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 11 (transLenTr ⟨56, by decide⟩ 11 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 11 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 11 (transLenTr ⟨56, by decide⟩ 11 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_11.D1 (m := 5) from colCertDiv_116_56_11.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 11 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_11.D2 (m := 5) from colCertDiv_116_56_11.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_11_match


theorem leaf_116_56_12 (hp : 12 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 12 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 12 (transLenTr ⟨56, by decide⟩ 12 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 12 (transLenTr ⟨56, by decide⟩ 12 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 12 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 12 (transLenTr ⟨56, by decide⟩ 12 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_12.D1 (m := 5) from colCertDiv_116_56_12.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 12 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_12.D2 (m := 5) from colCertDiv_116_56_12.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_12_match


theorem leaf_116_56_13 (hp : 13 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 13 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 13 (transLenTr ⟨56, by decide⟩ 13 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 13 (transLenTr ⟨56, by decide⟩ 13 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 13 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 13 (transLenTr ⟨56, by decide⟩ 13 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_13.D1 (m := 5) from colCertDiv_116_56_13.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 13 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_13.D2 (m := 5) from colCertDiv_116_56_13.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_13_match


theorem leaf_116_56_14 (hp : 14 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 14 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 14 (transLenTr ⟨56, by decide⟩ 14 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 14 (transLenTr ⟨56, by decide⟩ 14 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 14 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 14 (transLenTr ⟨56, by decide⟩ 14 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_14.D1 (m := 5) from colCertDiv_116_56_14.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 14 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_14.D2 (m := 5) from colCertDiv_116_56_14.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_14_match


theorem leaf_116_56_15 (hp : 15 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 15 (transLenTr ⟨56, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 15 (transLenTr ⟨56, by decide⟩ 15 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 15 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 15 (transLenTr ⟨56, by decide⟩ 15 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_15.D1 (m := 5) from colCertDiv_116_56_15.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 15 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_15.D2 (m := 5) from colCertDiv_116_56_15.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_15_match


theorem leaf_116_56_16 (hp : 16 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 16 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 16 (transLenTr ⟨56, by decide⟩ 16 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 16 (transLenTr ⟨56, by decide⟩ 16 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 16 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 16 (transLenTr ⟨56, by decide⟩ 16 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_16.D1 (m := 5) from colCertDiv_116_56_16.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 16 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_16.D2 (m := 5) from colCertDiv_116_56_16.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_16_match


theorem leaf_116_56_17 (hp : 17 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 17 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 17 (transLenTr ⟨56, by decide⟩ 17 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 17 (transLenTr ⟨56, by decide⟩ 17 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 17 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 17 (transLenTr ⟨56, by decide⟩ 17 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_17.D1 (m := 5) from colCertDiv_116_56_17.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 17 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_17.D2 (m := 5) from colCertDiv_116_56_17.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_17_match


theorem leaf_116_56_18 (hp : 18 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 18 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 18 (transLenTr ⟨56, by decide⟩ 18 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 18 (transLenTr ⟨56, by decide⟩ 18 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 18 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 18 (transLenTr ⟨56, by decide⟩ 18 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_18.D1 (m := 5) from colCertDiv_116_56_18.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 18 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_18.D2 (m := 5) from colCertDiv_116_56_18.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_18_match


theorem leaf_116_56_19 (hp : 19 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 19 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 19 (transLenTr ⟨56, by decide⟩ 19 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 19 (transLenTr ⟨56, by decide⟩ 19 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 19 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 19 (transLenTr ⟨56, by decide⟩ 19 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_19.D1 (m := 5) from colCertDiv_116_56_19.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 19 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_19.D2 (m := 5) from colCertDiv_116_56_19.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_19_match


theorem leaf_116_56_20 (hp : 20 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 20 (transLenTr ⟨56, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 20 (transLenTr ⟨56, by decide⟩ 20 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 20 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 20 (transLenTr ⟨56, by decide⟩ 20 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_20.D1 (m := 5) from colCertDiv_116_56_20.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 20 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_20.D2 (m := 5) from colCertDiv_116_56_20.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_20_match


theorem leaf_116_56_21 (hp : 21 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 21 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 21 (transLenTr ⟨56, by decide⟩ 21 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 21 (transLenTr ⟨56, by decide⟩ 21 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 21 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 21 (transLenTr ⟨56, by decide⟩ 21 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_21.D1 (m := 5) from colCertDiv_116_56_21.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 21 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_21.D2 (m := 5) from colCertDiv_116_56_21.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_21_match


theorem leaf_116_56_22 (hp : 22 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 22 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 22 (transLenTr ⟨56, by decide⟩ 22 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 22 (transLenTr ⟨56, by decide⟩ 22 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 22 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 22 (transLenTr ⟨56, by decide⟩ 22 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_22.D1 (m := 5) from colCertDiv_116_56_22.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 22 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_22.D2 (m := 5) from colCertDiv_116_56_22.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_22_match


theorem leaf_116_56_23 (hp : 23 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 23 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 23 (transLenTr ⟨56, by decide⟩ 23 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 23 (transLenTr ⟨56, by decide⟩ 23 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 23 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 23 (transLenTr ⟨56, by decide⟩ 23 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_23.D1 (m := 5) from colCertDiv_116_56_23.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 23 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_23.D2 (m := 5) from colCertDiv_116_56_23.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_23_match


theorem leaf_116_56_24 (hp : 24 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 24 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 24 (transLenTr ⟨56, by decide⟩ 24 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 24 (transLenTr ⟨56, by decide⟩ 24 hp)) T116_56
      hfix116_56 hinj116_56 hcardT116_56
      (fun i => conj_mem_of_fixedPoints _ _ (T116_56 i) (hfix116_56 i) _)
      ⟨116, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 24 hp) Q2.T116_56_2 Q2.hfix116_56_2 Q2.hinj116_56_2
      Q2.hcardT116_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_56_2 i) (Q2.hfix116_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 24 (transLenTr ⟨56, by decide⟩ 24 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T116_56 = colFn colCertDiv_116_56_24.D1 (m := 5) from colCertDiv_116_56_24.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 24 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T116_56_2 = colFn colCertDiv_116_56_24.D2 (m := 5) from colCertDiv_116_56_24.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_56_24_match


theorem leaf_116_57_0 (hp : 0 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 0 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 0 (transLenTr ⟨57, by decide⟩ 0 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 0 (transLenTr ⟨57, by decide⟩ 0 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 0 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      colCert_116_57_0.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_57_1 (hp : 1 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 1 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 1 (transLenTr ⟨57, by decide⟩ 1 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 1 (transLenTr ⟨57, by decide⟩ 1 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 1 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      colCert_116_57_1.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_57_2 (hp : 2 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 2 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 2 (transLenTr ⟨57, by decide⟩ 2 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 2 (transLenTr ⟨57, by decide⟩ 2 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 2 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      colCert_116_57_2.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_57_3 (hp : 3 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 3 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 3 (transLenTr ⟨57, by decide⟩ 3 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 3 (transLenTr ⟨57, by decide⟩ 3 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 3 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      colCert_116_57_3.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_57_4 (hp : 4 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 4 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 4 (transLenTr ⟨57, by decide⟩ 4 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 4 (transLenTr ⟨57, by decide⟩ 4 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 4 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      colCert_116_57_4.hD ?_).symm
  rw [alnId_116 j hj]


theorem leaf_116_57_5 (hp : 5 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 5 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 5 (transLenTr ⟨57, by decide⟩ 5 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 5 (transLenTr ⟨57, by decide⟩ 5 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 5 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 5 (transLenTr ⟨57, by decide⟩ 5 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_5.D1 (m := 5) from colCertDiv_116_57_5.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 5 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_5.D2 (m := 5) from colCertDiv_116_57_5.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_5_match


theorem leaf_116_57_6 (hp : 6 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 6 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 6 (transLenTr ⟨57, by decide⟩ 6 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 6 (transLenTr ⟨57, by decide⟩ 6 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 6 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 6 (transLenTr ⟨57, by decide⟩ 6 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_6.D1 (m := 5) from colCertDiv_116_57_6.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 6 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_6.D2 (m := 5) from colCertDiv_116_57_6.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_6_match


theorem leaf_116_57_7 (hp : 7 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 7 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 7 (transLenTr ⟨57, by decide⟩ 7 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 7 (transLenTr ⟨57, by decide⟩ 7 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 7 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 7 (transLenTr ⟨57, by decide⟩ 7 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_7.D1 (m := 5) from colCertDiv_116_57_7.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 7 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_7.D2 (m := 5) from colCertDiv_116_57_7.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_7_match


theorem leaf_116_57_8 (hp : 8 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 8 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 8 (transLenTr ⟨57, by decide⟩ 8 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 8 (transLenTr ⟨57, by decide⟩ 8 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 8 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 8 (transLenTr ⟨57, by decide⟩ 8 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_8.D1 (m := 5) from colCertDiv_116_57_8.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 8 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_8.D2 (m := 5) from colCertDiv_116_57_8.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_8_match


theorem leaf_116_57_9 (hp : 9 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 9 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 9 (transLenTr ⟨57, by decide⟩ 9 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 9 (transLenTr ⟨57, by decide⟩ 9 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 9 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 9 (transLenTr ⟨57, by decide⟩ 9 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_9.D1 (m := 5) from colCertDiv_116_57_9.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 9 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_9.D2 (m := 5) from colCertDiv_116_57_9.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_9_match


theorem leaf_116_57_10 (hp : 10 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 10 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 10 (transLenTr ⟨57, by decide⟩ 10 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 10 (transLenTr ⟨57, by decide⟩ 10 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 10 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 10 (transLenTr ⟨57, by decide⟩ 10 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_10.D1 (m := 5) from colCertDiv_116_57_10.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 10 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_10.D2 (m := 5) from colCertDiv_116_57_10.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_10_match


theorem leaf_116_57_11 (hp : 11 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 11 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 11 (transLenTr ⟨57, by decide⟩ 11 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 11 (transLenTr ⟨57, by decide⟩ 11 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 11 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 11 (transLenTr ⟨57, by decide⟩ 11 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_11.D1 (m := 5) from colCertDiv_116_57_11.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 11 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_11.D2 (m := 5) from colCertDiv_116_57_11.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_11_match


theorem leaf_116_57_12 (hp : 12 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 12 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 12 (transLenTr ⟨57, by decide⟩ 12 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 12 (transLenTr ⟨57, by decide⟩ 12 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 12 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 12 (transLenTr ⟨57, by decide⟩ 12 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_12.D1 (m := 5) from colCertDiv_116_57_12.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 12 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_12.D2 (m := 5) from colCertDiv_116_57_12.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_12_match


theorem leaf_116_57_13 (hp : 13 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 13 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 13 (transLenTr ⟨57, by decide⟩ 13 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 13 (transLenTr ⟨57, by decide⟩ 13 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 13 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 13 (transLenTr ⟨57, by decide⟩ 13 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_13.D1 (m := 5) from colCertDiv_116_57_13.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 13 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_13.D2 (m := 5) from colCertDiv_116_57_13.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_13_match


theorem leaf_116_57_14 (hp : 14 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 14 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 14 (transLenTr ⟨57, by decide⟩ 14 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 14 (transLenTr ⟨57, by decide⟩ 14 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 14 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 14 (transLenTr ⟨57, by decide⟩ 14 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_14.D1 (m := 5) from colCertDiv_116_57_14.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 14 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_14.D2 (m := 5) from colCertDiv_116_57_14.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_14_match


theorem leaf_116_57_15 (hp : 15 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 15 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 15 (transLenTr ⟨57, by decide⟩ 15 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 15 (transLenTr ⟨57, by decide⟩ 15 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 15 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 15 (transLenTr ⟨57, by decide⟩ 15 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_15.D1 (m := 5) from colCertDiv_116_57_15.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 15 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_15.D2 (m := 5) from colCertDiv_116_57_15.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_15_match


theorem leaf_116_57_16 (hp : 16 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 16 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 16 (transLenTr ⟨57, by decide⟩ 16 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 16 (transLenTr ⟨57, by decide⟩ 16 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 16 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 16 (transLenTr ⟨57, by decide⟩ 16 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_16.D1 (m := 5) from colCertDiv_116_57_16.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 16 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_16.D2 (m := 5) from colCertDiv_116_57_16.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_16_match


theorem leaf_116_57_17 (hp : 17 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 17 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 17 (transLenTr ⟨57, by decide⟩ 17 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 17 (transLenTr ⟨57, by decide⟩ 17 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 17 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 17 (transLenTr ⟨57, by decide⟩ 17 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_17.D1 (m := 5) from colCertDiv_116_57_17.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 17 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_17.D2 (m := 5) from colCertDiv_116_57_17.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_17_match


theorem leaf_116_57_18 (hp : 18 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 18 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 18 (transLenTr ⟨57, by decide⟩ 18 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 18 (transLenTr ⟨57, by decide⟩ 18 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 18 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 18 (transLenTr ⟨57, by decide⟩ 18 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_18.D1 (m := 5) from colCertDiv_116_57_18.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 18 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_18.D2 (m := 5) from colCertDiv_116_57_18.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_18_match


theorem leaf_116_57_19 (hp : 19 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 19 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 19 (transLenTr ⟨57, by decide⟩ 19 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 19 (transLenTr ⟨57, by decide⟩ 19 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 19 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 19 (transLenTr ⟨57, by decide⟩ 19 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_19.D1 (m := 5) from colCertDiv_116_57_19.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 19 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_19.D2 (m := 5) from colCertDiv_116_57_19.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_19_match


theorem leaf_116_57_20 (hp : 20 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 20 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 20 (transLenTr ⟨57, by decide⟩ 20 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 20 (transLenTr ⟨57, by decide⟩ 20 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 20 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 20 (transLenTr ⟨57, by decide⟩ 20 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_20.D1 (m := 5) from colCertDiv_116_57_20.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 20 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_20.D2 (m := 5) from colCertDiv_116_57_20.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_20_match


theorem leaf_116_57_21 (hp : 21 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 21 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 21 (transLenTr ⟨57, by decide⟩ 21 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 21 (transLenTr ⟨57, by decide⟩ 21 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 21 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 21 (transLenTr ⟨57, by decide⟩ 21 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_21.D1 (m := 5) from colCertDiv_116_57_21.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 21 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_21.D2 (m := 5) from colCertDiv_116_57_21.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_21_match


theorem leaf_116_57_22 (hp : 22 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 22 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 22 (transLenTr ⟨57, by decide⟩ 22 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 22 (transLenTr ⟨57, by decide⟩ 22 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 22 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 22 (transLenTr ⟨57, by decide⟩ 22 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_22.D1 (m := 5) from colCertDiv_116_57_22.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 22 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_22.D2 (m := 5) from colCertDiv_116_57_22.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_22_match


theorem leaf_116_57_23 (hp : 23 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 116 []).length)
    (hq : (normIsRep.getD 116 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 23 hp)
        (rowE2 (⟨116, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 23 (transLenTr ⟨57, by decide⟩ 23 hp))
        (rowE1 (⟨116, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨116, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨116, by decide⟩ (listedAt ⟨116, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 23 (transLenTr ⟨57, by decide⟩ 23 hp)) T116_57
      hfix116_57 hinj116_57 hcardT116_57
      (fun i => conj_mem_of_fixedPoints _ _ (T116_57 i) (hfix116_57 i) _)
      ⟨116, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨116, by decide⟩ (Q2.listedAt ⟨116, by decide⟩
        (alnCheck_rep ⟨116, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 23 hp) Q2.T116_57_2 Q2.hfix116_57_2 Q2.hinj116_57_2
      Q2.hcardT116_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T116_57_2 i) (Q2.hfix116_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨116, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 23 (transLenTr ⟨57, by decide⟩ 23 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T116_57 = colFn colCertDiv_116_57_23.D1 (m := 5) from colCertDiv_116_57_23.bind1,
    show colData2 (⟨116, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 23 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T116_57_2 = colFn colCertDiv_116_57_23.D2 (m := 5) from colCertDiv_116_57_23.bind2]
  rw [alnId_116 j hj]
  exact fastcode_of_div ⟨116, by decide⟩ _ _ _
    ((alnId_116 j hj) ▸ Q2.listedAt (⟨116, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨116, by decide⟩ : Fin 148) hj hq).1) colCertDiv_116_57_23_match


end LeanDring.P5Presentation
