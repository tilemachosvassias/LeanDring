/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C021
import LeanDring.P5.Data.ColCdd.C022
import LeanDring.P5.Data.ColRestCheap.C101
import LeanDring.P5.Data.ColRestCheap.C102
import LeanDring.P5.Data.ColRestCheap.C103
import LeanDring.P5.Data.ColRestCheap.C104
import LeanDring.P5.Data.ColRestCheap.C105
import LeanDring.P5.Data.EntryK.C042
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C034
import LeanDring.P5.Data.SpeciesDiv.C035
import LeanDring.P5.Data.SpeciesDiv.C036

/-! # Stage-5 leaves, chunk 46 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_144_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T144_10
      hfix144_10 hinj144_10 hcardT144_10
      (fun i => conj_mem_of_fixedPoints _ _ (T144_10 i) (hfix144_10 i) _)
      ⟨144, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T144_10_2 Q2.hfix144_10_2 Q2.hinj144_10_2
      Q2.hcardT144_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_10_2 i) (Q2.hfix144_10_2 i) _)
      colCert_144_10_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T144_10
      hfix144_10 hinj144_10 hcardT144_10
      (fun i => conj_mem_of_fixedPoints _ _ (T144_10 i) (hfix144_10 i) _)
      ⟨144, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T144_10_2 Q2.hfix144_10_2 Q2.hinj144_10_2
      Q2.hcardT144_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_10_2 i) (Q2.hfix144_10_2 i) _)
      colCert_144_10_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T144_11
      hfix144_11 hinj144_11 hcardT144_11
      (fun i => conj_mem_of_fixedPoints _ _ (T144_11 i) (hfix144_11 i) _)
      ⟨144, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T144_11_2 Q2.hfix144_11_2 Q2.hinj144_11_2
      Q2.hcardT144_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_11_2 i) (Q2.hfix144_11_2 i) _)
      colCert_144_11_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T144_11
      hfix144_11 hinj144_11 hcardT144_11
      (fun i => conj_mem_of_fixedPoints _ _ (T144_11 i) (hfix144_11 i) _)
      ⟨144, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T144_11_2 Q2.hfix144_11_2 Q2.hinj144_11_2
      Q2.hcardT144_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_11_2 i) (Q2.hfix144_11_2 i) _)
      colCert_144_11_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T144_11
      hfix144_11 hinj144_11 hcardT144_11
      (fun i => conj_mem_of_fixedPoints _ _ (T144_11 i) (hfix144_11 i) _)
      ⟨144, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T144_11_2 Q2.hfix144_11_2 Q2.hinj144_11_2
      Q2.hcardT144_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_11_2 i) (Q2.hfix144_11_2 i) _)
      colCert_144_11_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T144_11
      hfix144_11 hinj144_11 hcardT144_11
      (fun i => conj_mem_of_fixedPoints _ _ (T144_11 i) (hfix144_11 i) _)
      ⟨144, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T144_11_2 Q2.hfix144_11_2 Q2.hinj144_11_2
      Q2.hcardT144_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_11_2 i) (Q2.hfix144_11_2 i) _)
      colCert_144_11_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T144_11
      hfix144_11 hinj144_11 hcardT144_11
      (fun i => conj_mem_of_fixedPoints _ _ (T144_11 i) (hfix144_11 i) _)
      ⟨144, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T144_11_2 Q2.hfix144_11_2 Q2.hinj144_11_2
      Q2.hcardT144_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_11_2 i) (Q2.hfix144_11_2 i) _)
      colCert_144_11_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T144_12
      hfix144_12 hinj144_12 hcardT144_12
      (fun i => conj_mem_of_fixedPoints _ _ (T144_12 i) (hfix144_12 i) _)
      ⟨144, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T144_12_2 Q2.hfix144_12_2 Q2.hinj144_12_2
      Q2.hcardT144_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_12_2 i) (Q2.hfix144_12_2 i) _)
      colCert_144_12_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T144_12
      hfix144_12 hinj144_12 hcardT144_12
      (fun i => conj_mem_of_fixedPoints _ _ (T144_12 i) (hfix144_12 i) _)
      ⟨144, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T144_12_2 Q2.hfix144_12_2 Q2.hinj144_12_2
      Q2.hcardT144_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_12_2 i) (Q2.hfix144_12_2 i) _)
      colCert_144_12_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T144_12
      hfix144_12 hinj144_12 hcardT144_12
      (fun i => conj_mem_of_fixedPoints _ _ (T144_12 i) (hfix144_12 i) _)
      ⟨144, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T144_12_2 Q2.hfix144_12_2 Q2.hinj144_12_2
      Q2.hcardT144_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_12_2 i) (Q2.hfix144_12_2 i) _)
      colCert_144_12_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T144_12
      hfix144_12 hinj144_12 hcardT144_12
      (fun i => conj_mem_of_fixedPoints _ _ (T144_12 i) (hfix144_12 i) _)
      ⟨144, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T144_12_2 Q2.hfix144_12_2 Q2.hinj144_12_2
      Q2.hcardT144_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_12_2 i) (Q2.hfix144_12_2 i) _)
      colCert_144_12_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T144_12
      hfix144_12 hinj144_12 hcardT144_12
      (fun i => conj_mem_of_fixedPoints _ _ (T144_12 i) (hfix144_12 i) _)
      ⟨144, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T144_12_2 Q2.hfix144_12_2 Q2.hinj144_12_2
      Q2.hcardT144_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_12_2 i) (Q2.hfix144_12_2 i) _)
      colCert_144_12_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T144_38
      hfix144_38 hinj144_38 hcardT144_38
      (fun i => conj_mem_of_fixedPoints _ _ (T144_38 i) (hfix144_38 i) _)
      ⟨144, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T144_38_2 Q2.hfix144_38_2 Q2.hinj144_38_2
      Q2.hcardT144_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_38_2 i) (Q2.hfix144_38_2 i) _)
      colCert_144_38_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T144_38
      hfix144_38 hinj144_38 hcardT144_38
      (fun i => conj_mem_of_fixedPoints _ _ (T144_38 i) (hfix144_38 i) _)
      ⟨144, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T144_38_2 Q2.hfix144_38_2 Q2.hinj144_38_2
      Q2.hcardT144_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_38_2 i) (Q2.hfix144_38_2 i) _)
      colCert_144_38_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T144_38
      hfix144_38 hinj144_38 hcardT144_38
      (fun i => conj_mem_of_fixedPoints _ _ (T144_38 i) (hfix144_38 i) _)
      ⟨144, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T144_38_2 Q2.hfix144_38_2 Q2.hinj144_38_2
      Q2.hcardT144_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_38_2 i) (Q2.hfix144_38_2 i) _)
      colCert_144_38_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T144_38
      hfix144_38 hinj144_38 hcardT144_38
      (fun i => conj_mem_of_fixedPoints _ _ (T144_38 i) (hfix144_38 i) _)
      ⟨144, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T144_38_2 Q2.hfix144_38_2 Q2.hinj144_38_2
      Q2.hcardT144_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_38_2 i) (Q2.hfix144_38_2 i) _)
      colCert_144_38_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T144_38
      hfix144_38 hinj144_38 hcardT144_38
      (fun i => conj_mem_of_fixedPoints _ _ (T144_38 i) (hfix144_38 i) _)
      ⟨144, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T144_38_2 Q2.hfix144_38_2 Q2.hinj144_38_2
      Q2.hcardT144_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_38_2 i) (Q2.hfix144_38_2 i) _)
      colCert_144_38_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T144_38
      hfix144_38 hinj144_38 hcardT144_38
      (fun i => conj_mem_of_fixedPoints _ _ (T144_38 i) (hfix144_38 i) _)
      ⟨144, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T144_38_2 Q2.hfix144_38_2 Q2.hinj144_38_2
      Q2.hcardT144_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_38_2 i) (Q2.hfix144_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T144_38 = colFn colCertDiv_144_38_5.D1 (m := 5) from colCertDiv_144_38_5.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T144_38_2 = colFn colCertDiv_144_38_5.D2 (m := 5) from colCertDiv_144_38_5.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_38_5_match


theorem leaf_144_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T144_38
      hfix144_38 hinj144_38 hcardT144_38
      (fun i => conj_mem_of_fixedPoints _ _ (T144_38 i) (hfix144_38 i) _)
      ⟨144, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T144_38_2 Q2.hfix144_38_2 Q2.hinj144_38_2
      Q2.hcardT144_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_38_2 i) (Q2.hfix144_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T144_38 = colFn colCertDiv_144_38_10.D1 (m := 5) from colCertDiv_144_38_10.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T144_38_2 = colFn colCertDiv_144_38_10.D2 (m := 5) from colCertDiv_144_38_10.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_38_10_match


theorem leaf_144_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T144_38
      hfix144_38 hinj144_38 hcardT144_38
      (fun i => conj_mem_of_fixedPoints _ _ (T144_38 i) (hfix144_38 i) _)
      ⟨144, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T144_38_2 Q2.hfix144_38_2 Q2.hinj144_38_2
      Q2.hcardT144_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_38_2 i) (Q2.hfix144_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T144_38 = colFn colCertDiv_144_38_15.D1 (m := 5) from colCertDiv_144_38_15.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T144_38_2 = colFn colCertDiv_144_38_15.D2 (m := 5) from colCertDiv_144_38_15.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_38_15_match


theorem leaf_144_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T144_38
      hfix144_38 hinj144_38 hcardT144_38
      (fun i => conj_mem_of_fixedPoints _ _ (T144_38 i) (hfix144_38 i) _)
      ⟨144, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T144_38_2 Q2.hfix144_38_2 Q2.hinj144_38_2
      Q2.hcardT144_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_38_2 i) (Q2.hfix144_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T144_38 = colFn colCertDiv_144_38_20.D1 (m := 5) from colCertDiv_144_38_20.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T144_38_2 = colFn colCertDiv_144_38_20.D2 (m := 5) from colCertDiv_144_38_20.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_38_20_match


theorem leaf_144_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T144_39
      hfix144_39 hinj144_39 hcardT144_39
      (fun i => conj_mem_of_fixedPoints _ _ (T144_39 i) (hfix144_39 i) _)
      ⟨144, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T144_39_2 Q2.hfix144_39_2 Q2.hinj144_39_2
      Q2.hcardT144_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_39_2 i) (Q2.hfix144_39_2 i) _)
      colCert_144_39_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T144_39
      hfix144_39 hinj144_39 hcardT144_39
      (fun i => conj_mem_of_fixedPoints _ _ (T144_39 i) (hfix144_39 i) _)
      ⟨144, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T144_39_2 Q2.hfix144_39_2 Q2.hinj144_39_2
      Q2.hcardT144_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_39_2 i) (Q2.hfix144_39_2 i) _)
      colCert_144_39_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T144_39
      hfix144_39 hinj144_39 hcardT144_39
      (fun i => conj_mem_of_fixedPoints _ _ (T144_39 i) (hfix144_39 i) _)
      ⟨144, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T144_39_2 Q2.hfix144_39_2 Q2.hinj144_39_2
      Q2.hcardT144_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_39_2 i) (Q2.hfix144_39_2 i) _)
      colCert_144_39_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T144_39
      hfix144_39 hinj144_39 hcardT144_39
      (fun i => conj_mem_of_fixedPoints _ _ (T144_39 i) (hfix144_39 i) _)
      ⟨144, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T144_39_2 Q2.hfix144_39_2 Q2.hinj144_39_2
      Q2.hcardT144_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_39_2 i) (Q2.hfix144_39_2 i) _)
      colCert_144_39_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T144_39
      hfix144_39 hinj144_39 hcardT144_39
      (fun i => conj_mem_of_fixedPoints _ _ (T144_39 i) (hfix144_39 i) _)
      ⟨144, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T144_39_2 Q2.hfix144_39_2 Q2.hinj144_39_2
      Q2.hcardT144_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_39_2 i) (Q2.hfix144_39_2 i) _)
      colCert_144_39_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T144_39
      hfix144_39 hinj144_39 hcardT144_39
      (fun i => conj_mem_of_fixedPoints _ _ (T144_39 i) (hfix144_39 i) _)
      ⟨144, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T144_39_2 Q2.hfix144_39_2 Q2.hinj144_39_2
      Q2.hcardT144_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_39_2 i) (Q2.hfix144_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T144_39 = colFn colCertDiv_144_39_5.D1 (m := 5) from colCertDiv_144_39_5.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 5 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T144_39_2 = colFn colCertDiv_144_39_5.D2 (m := 5) from colCertDiv_144_39_5.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_39_5_match


theorem leaf_144_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T144_39
      hfix144_39 hinj144_39 hcardT144_39
      (fun i => conj_mem_of_fixedPoints _ _ (T144_39 i) (hfix144_39 i) _)
      ⟨144, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T144_39_2 Q2.hfix144_39_2 Q2.hinj144_39_2
      Q2.hcardT144_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_39_2 i) (Q2.hfix144_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T144_39 = colFn colCertDiv_144_39_10.D1 (m := 5) from colCertDiv_144_39_10.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 10 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T144_39_2 = colFn colCertDiv_144_39_10.D2 (m := 5) from colCertDiv_144_39_10.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_39_10_match


theorem leaf_144_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T144_39
      hfix144_39 hinj144_39 hcardT144_39
      (fun i => conj_mem_of_fixedPoints _ _ (T144_39 i) (hfix144_39 i) _)
      ⟨144, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T144_39_2 Q2.hfix144_39_2 Q2.hinj144_39_2
      Q2.hcardT144_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_39_2 i) (Q2.hfix144_39_2 i) _)
      colCert_144_39_15.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T144_39
      hfix144_39 hinj144_39 hcardT144_39
      (fun i => conj_mem_of_fixedPoints _ _ (T144_39 i) (hfix144_39 i) _)
      ⟨144, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T144_39_2 Q2.hfix144_39_2 Q2.hinj144_39_2
      Q2.hcardT144_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_39_2 i) (Q2.hfix144_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T144_39 = colFn colCertDiv_144_39_20.D1 (m := 5) from colCertDiv_144_39_20.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 20 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T144_39_2 = colFn colCertDiv_144_39_20.D2 (m := 5) from colCertDiv_144_39_20.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_39_20_match


theorem leaf_144_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T144_40
      hfix144_40 hinj144_40 hcardT144_40
      (fun i => conj_mem_of_fixedPoints _ _ (T144_40 i) (hfix144_40 i) _)
      ⟨144, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T144_40_2 Q2.hfix144_40_2 Q2.hinj144_40_2
      Q2.hcardT144_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_40_2 i) (Q2.hfix144_40_2 i) _)
      colCert_144_40_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T144_40
      hfix144_40 hinj144_40 hcardT144_40
      (fun i => conj_mem_of_fixedPoints _ _ (T144_40 i) (hfix144_40 i) _)
      ⟨144, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T144_40_2 Q2.hfix144_40_2 Q2.hinj144_40_2
      Q2.hcardT144_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_40_2 i) (Q2.hfix144_40_2 i) _)
      colCert_144_40_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T144_40
      hfix144_40 hinj144_40 hcardT144_40
      (fun i => conj_mem_of_fixedPoints _ _ (T144_40 i) (hfix144_40 i) _)
      ⟨144, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T144_40_2 Q2.hfix144_40_2 Q2.hinj144_40_2
      Q2.hcardT144_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_40_2 i) (Q2.hfix144_40_2 i) _)
      colCert_144_40_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T144_40
      hfix144_40 hinj144_40 hcardT144_40
      (fun i => conj_mem_of_fixedPoints _ _ (T144_40 i) (hfix144_40 i) _)
      ⟨144, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T144_40_2 Q2.hfix144_40_2 Q2.hinj144_40_2
      Q2.hcardT144_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_40_2 i) (Q2.hfix144_40_2 i) _)
      colCert_144_40_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T144_40
      hfix144_40 hinj144_40 hcardT144_40
      (fun i => conj_mem_of_fixedPoints _ _ (T144_40 i) (hfix144_40 i) _)
      ⟨144, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T144_40_2 Q2.hfix144_40_2 Q2.hinj144_40_2
      Q2.hcardT144_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_40_2 i) (Q2.hfix144_40_2 i) _)
      colCert_144_40_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T144_40
      hfix144_40 hinj144_40 hcardT144_40
      (fun i => conj_mem_of_fixedPoints _ _ (T144_40 i) (hfix144_40 i) _)
      ⟨144, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T144_40_2 Q2.hfix144_40_2 Q2.hinj144_40_2
      Q2.hcardT144_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_40_2 i) (Q2.hfix144_40_2 i) _)
      colCert_144_40_5.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T144_40
      hfix144_40 hinj144_40 hcardT144_40
      (fun i => conj_mem_of_fixedPoints _ _ (T144_40 i) (hfix144_40 i) _)
      ⟨144, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T144_40_2 Q2.hfix144_40_2 Q2.hinj144_40_2
      Q2.hcardT144_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_40_2 i) (Q2.hfix144_40_2 i) _)
      colCert_144_40_10.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T144_40
      hfix144_40 hinj144_40 hcardT144_40
      (fun i => conj_mem_of_fixedPoints _ _ (T144_40 i) (hfix144_40 i) _)
      ⟨144, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T144_40_2 Q2.hfix144_40_2 Q2.hinj144_40_2
      Q2.hcardT144_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_40_2 i) (Q2.hfix144_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T144_40 = colFn colCertDiv_144_40_15.D1 (m := 5) from colCertDiv_144_40_15.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 15 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T144_40_2 = colFn colCertDiv_144_40_15.D2 (m := 5) from colCertDiv_144_40_15.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_40_15_match


theorem leaf_144_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T144_40
      hfix144_40 hinj144_40 hcardT144_40
      (fun i => conj_mem_of_fixedPoints _ _ (T144_40 i) (hfix144_40 i) _)
      ⟨144, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T144_40_2 Q2.hfix144_40_2 Q2.hinj144_40_2
      Q2.hcardT144_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_40_2 i) (Q2.hfix144_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T144_40 = colFn colCertDiv_144_40_20.D1 (m := 5) from colCertDiv_144_40_20.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 20 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T144_40_2 = colFn colCertDiv_144_40_20.D2 (m := 5) from colCertDiv_144_40_20.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_40_20_match


theorem leaf_144_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T144_41
      hfix144_41 hinj144_41 hcardT144_41
      (fun i => conj_mem_of_fixedPoints _ _ (T144_41 i) (hfix144_41 i) _)
      ⟨144, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T144_41_2 Q2.hfix144_41_2 Q2.hinj144_41_2
      Q2.hcardT144_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_41_2 i) (Q2.hfix144_41_2 i) _)
      colCert_144_41_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T144_41
      hfix144_41 hinj144_41 hcardT144_41
      (fun i => conj_mem_of_fixedPoints _ _ (T144_41 i) (hfix144_41 i) _)
      ⟨144, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T144_41_2 Q2.hfix144_41_2 Q2.hinj144_41_2
      Q2.hcardT144_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_41_2 i) (Q2.hfix144_41_2 i) _)
      colCert_144_41_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T144_41
      hfix144_41 hinj144_41 hcardT144_41
      (fun i => conj_mem_of_fixedPoints _ _ (T144_41 i) (hfix144_41 i) _)
      ⟨144, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T144_41_2 Q2.hfix144_41_2 Q2.hinj144_41_2
      Q2.hcardT144_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_41_2 i) (Q2.hfix144_41_2 i) _)
      colCert_144_41_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T144_41
      hfix144_41 hinj144_41 hcardT144_41
      (fun i => conj_mem_of_fixedPoints _ _ (T144_41 i) (hfix144_41 i) _)
      ⟨144, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T144_41_2 Q2.hfix144_41_2 Q2.hinj144_41_2
      Q2.hcardT144_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_41_2 i) (Q2.hfix144_41_2 i) _)
      colCert_144_41_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T144_41
      hfix144_41 hinj144_41 hcardT144_41
      (fun i => conj_mem_of_fixedPoints _ _ (T144_41 i) (hfix144_41 i) _)
      ⟨144, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T144_41_2 Q2.hfix144_41_2 Q2.hinj144_41_2
      Q2.hcardT144_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_41_2 i) (Q2.hfix144_41_2 i) _)
      colCert_144_41_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T144_41
      hfix144_41 hinj144_41 hcardT144_41
      (fun i => conj_mem_of_fixedPoints _ _ (T144_41 i) (hfix144_41 i) _)
      ⟨144, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T144_41_2 Q2.hfix144_41_2 Q2.hinj144_41_2
      Q2.hcardT144_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_41_2 i) (Q2.hfix144_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T144_41 = colFn colCertDiv_144_41_5.D1 (m := 5) from colCertDiv_144_41_5.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 5 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T144_41_2 = colFn colCertDiv_144_41_5.D2 (m := 5) from colCertDiv_144_41_5.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_41_5_match


theorem leaf_144_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T144_41
      hfix144_41 hinj144_41 hcardT144_41
      (fun i => conj_mem_of_fixedPoints _ _ (T144_41 i) (hfix144_41 i) _)
      ⟨144, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T144_41_2 Q2.hfix144_41_2 Q2.hinj144_41_2
      Q2.hcardT144_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_41_2 i) (Q2.hfix144_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T144_41 = colFn colCertDiv_144_41_10.D1 (m := 5) from colCertDiv_144_41_10.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 10 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T144_41_2 = colFn colCertDiv_144_41_10.D2 (m := 5) from colCertDiv_144_41_10.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_41_10_match


theorem leaf_144_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T144_41
      hfix144_41 hinj144_41 hcardT144_41
      (fun i => conj_mem_of_fixedPoints _ _ (T144_41 i) (hfix144_41 i) _)
      ⟨144, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T144_41_2 Q2.hfix144_41_2 Q2.hinj144_41_2
      Q2.hcardT144_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_41_2 i) (Q2.hfix144_41_2 i) _)
      colCert_144_41_15.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T144_41
      hfix144_41 hinj144_41 hcardT144_41
      (fun i => conj_mem_of_fixedPoints _ _ (T144_41 i) (hfix144_41 i) _)
      ⟨144, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T144_41_2 Q2.hfix144_41_2 Q2.hinj144_41_2
      Q2.hcardT144_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_41_2 i) (Q2.hfix144_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T144_41 = colFn colCertDiv_144_41_20.D1 (m := 5) from colCertDiv_144_41_20.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 20 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T144_41_2 = colFn colCertDiv_144_41_20.D2 (m := 5) from colCertDiv_144_41_20.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_41_20_match


theorem leaf_144_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T144_42
      hfix144_42 hinj144_42 hcardT144_42
      (fun i => conj_mem_of_fixedPoints _ _ (T144_42 i) (hfix144_42 i) _)
      ⟨144, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T144_42_2 Q2.hfix144_42_2 Q2.hinj144_42_2
      Q2.hcardT144_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_42_2 i) (Q2.hfix144_42_2 i) _)
      colCert_144_42_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T144_42
      hfix144_42 hinj144_42 hcardT144_42
      (fun i => conj_mem_of_fixedPoints _ _ (T144_42 i) (hfix144_42 i) _)
      ⟨144, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T144_42_2 Q2.hfix144_42_2 Q2.hinj144_42_2
      Q2.hcardT144_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_42_2 i) (Q2.hfix144_42_2 i) _)
      colCert_144_42_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T144_42
      hfix144_42 hinj144_42 hcardT144_42
      (fun i => conj_mem_of_fixedPoints _ _ (T144_42 i) (hfix144_42 i) _)
      ⟨144, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T144_42_2 Q2.hfix144_42_2 Q2.hinj144_42_2
      Q2.hcardT144_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_42_2 i) (Q2.hfix144_42_2 i) _)
      colCert_144_42_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T144_42
      hfix144_42 hinj144_42 hcardT144_42
      (fun i => conj_mem_of_fixedPoints _ _ (T144_42 i) (hfix144_42 i) _)
      ⟨144, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T144_42_2 Q2.hfix144_42_2 Q2.hinj144_42_2
      Q2.hcardT144_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_42_2 i) (Q2.hfix144_42_2 i) _)
      colCert_144_42_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T144_42
      hfix144_42 hinj144_42 hcardT144_42
      (fun i => conj_mem_of_fixedPoints _ _ (T144_42 i) (hfix144_42 i) _)
      ⟨144, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T144_42_2 Q2.hfix144_42_2 Q2.hinj144_42_2
      Q2.hcardT144_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_42_2 i) (Q2.hfix144_42_2 i) _)
      colCert_144_42_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T144_42
      hfix144_42 hinj144_42 hcardT144_42
      (fun i => conj_mem_of_fixedPoints _ _ (T144_42 i) (hfix144_42 i) _)
      ⟨144, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T144_42_2 Q2.hfix144_42_2 Q2.hinj144_42_2
      Q2.hcardT144_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_42_2 i) (Q2.hfix144_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T144_42 = colFn colCertDiv_144_42_5.D1 (m := 5) from colCertDiv_144_42_5.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T144_42_2 = colFn colCertDiv_144_42_5.D2 (m := 5) from colCertDiv_144_42_5.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_42_5_match


theorem leaf_144_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T144_42
      hfix144_42 hinj144_42 hcardT144_42
      (fun i => conj_mem_of_fixedPoints _ _ (T144_42 i) (hfix144_42 i) _)
      ⟨144, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T144_42_2 Q2.hfix144_42_2 Q2.hinj144_42_2
      Q2.hcardT144_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_42_2 i) (Q2.hfix144_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T144_42 = colFn colCertDiv_144_42_10.D1 (m := 5) from colCertDiv_144_42_10.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T144_42_2 = colFn colCertDiv_144_42_10.D2 (m := 5) from colCertDiv_144_42_10.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_42_10_match


theorem leaf_144_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T144_42
      hfix144_42 hinj144_42 hcardT144_42
      (fun i => conj_mem_of_fixedPoints _ _ (T144_42 i) (hfix144_42 i) _)
      ⟨144, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T144_42_2 Q2.hfix144_42_2 Q2.hinj144_42_2
      Q2.hcardT144_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_42_2 i) (Q2.hfix144_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T144_42 = colFn colCertDiv_144_42_15.D1 (m := 5) from colCertDiv_144_42_15.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T144_42_2 = colFn colCertDiv_144_42_15.D2 (m := 5) from colCertDiv_144_42_15.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_42_15_match


theorem leaf_144_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T144_42
      hfix144_42 hinj144_42 hcardT144_42
      (fun i => conj_mem_of_fixedPoints _ _ (T144_42 i) (hfix144_42 i) _)
      ⟨144, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T144_42_2 Q2.hfix144_42_2 Q2.hinj144_42_2
      Q2.hcardT144_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_42_2 i) (Q2.hfix144_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T144_42 = colFn colCertDiv_144_42_20.D1 (m := 5) from colCertDiv_144_42_20.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T144_42_2 = colFn colCertDiv_144_42_20.D2 (m := 5) from colCertDiv_144_42_20.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_42_20_match


theorem leaf_144_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T144_53
      hfix144_53 hinj144_53 hcardT144_53
      (fun i => conj_mem_of_fixedPoints _ _ (T144_53 i) (hfix144_53 i) _)
      ⟨144, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T144_53_2 Q2.hfix144_53_2 Q2.hinj144_53_2
      Q2.hcardT144_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_53_2 i) (Q2.hfix144_53_2 i) _)
      colCert_144_53_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T144_53
      hfix144_53 hinj144_53 hcardT144_53
      (fun i => conj_mem_of_fixedPoints _ _ (T144_53 i) (hfix144_53 i) _)
      ⟨144, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T144_53_2 Q2.hfix144_53_2 Q2.hinj144_53_2
      Q2.hcardT144_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_53_2 i) (Q2.hfix144_53_2 i) _)
      colCert_144_53_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T144_53
      hfix144_53 hinj144_53 hcardT144_53
      (fun i => conj_mem_of_fixedPoints _ _ (T144_53 i) (hfix144_53 i) _)
      ⟨144, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T144_53_2 Q2.hfix144_53_2 Q2.hinj144_53_2
      Q2.hcardT144_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_53_2 i) (Q2.hfix144_53_2 i) _)
      colCert_144_53_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T144_53
      hfix144_53 hinj144_53 hcardT144_53
      (fun i => conj_mem_of_fixedPoints _ _ (T144_53 i) (hfix144_53 i) _)
      ⟨144, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T144_53_2 Q2.hfix144_53_2 Q2.hinj144_53_2
      Q2.hcardT144_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_53_2 i) (Q2.hfix144_53_2 i) _)
      colCert_144_53_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T144_53
      hfix144_53 hinj144_53 hcardT144_53
      (fun i => conj_mem_of_fixedPoints _ _ (T144_53 i) (hfix144_53 i) _)
      ⟨144, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T144_53_2 Q2.hfix144_53_2 Q2.hinj144_53_2
      Q2.hcardT144_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_53_2 i) (Q2.hfix144_53_2 i) _)
      colCert_144_53_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T144_53
      hfix144_53 hinj144_53 hcardT144_53
      (fun i => conj_mem_of_fixedPoints _ _ (T144_53 i) (hfix144_53 i) _)
      ⟨144, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T144_53_2 Q2.hfix144_53_2 Q2.hinj144_53_2
      Q2.hcardT144_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_53_2 i) (Q2.hfix144_53_2 i) _)
      colCert_144_53_5.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T144_53
      hfix144_53 hinj144_53 hcardT144_53
      (fun i => conj_mem_of_fixedPoints _ _ (T144_53 i) (hfix144_53 i) _)
      ⟨144, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T144_53_2 Q2.hfix144_53_2 Q2.hinj144_53_2
      Q2.hcardT144_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_53_2 i) (Q2.hfix144_53_2 i) _)
      colCert_144_53_10.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T144_53
      hfix144_53 hinj144_53 hcardT144_53
      (fun i => conj_mem_of_fixedPoints _ _ (T144_53 i) (hfix144_53 i) _)
      ⟨144, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T144_53_2 Q2.hfix144_53_2 Q2.hinj144_53_2
      Q2.hcardT144_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_53_2 i) (Q2.hfix144_53_2 i) _)
      colCert_144_53_15.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T144_53
      hfix144_53 hinj144_53 hcardT144_53
      (fun i => conj_mem_of_fixedPoints _ _ (T144_53 i) (hfix144_53 i) _)
      ⟨144, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T144_53_2 Q2.hfix144_53_2 Q2.hinj144_53_2
      Q2.hcardT144_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_53_2 i) (Q2.hfix144_53_2 i) _)
      colCert_144_53_20.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T144_54
      hfix144_54 hinj144_54 hcardT144_54
      (fun i => conj_mem_of_fixedPoints _ _ (T144_54 i) (hfix144_54 i) _)
      ⟨144, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T144_54_2 Q2.hfix144_54_2 Q2.hinj144_54_2
      Q2.hcardT144_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_54_2 i) (Q2.hfix144_54_2 i) _)
      colCert_144_54_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T144_54
      hfix144_54 hinj144_54 hcardT144_54
      (fun i => conj_mem_of_fixedPoints _ _ (T144_54 i) (hfix144_54 i) _)
      ⟨144, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T144_54_2 Q2.hfix144_54_2 Q2.hinj144_54_2
      Q2.hcardT144_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_54_2 i) (Q2.hfix144_54_2 i) _)
      colCert_144_54_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T144_54
      hfix144_54 hinj144_54 hcardT144_54
      (fun i => conj_mem_of_fixedPoints _ _ (T144_54 i) (hfix144_54 i) _)
      ⟨144, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T144_54_2 Q2.hfix144_54_2 Q2.hinj144_54_2
      Q2.hcardT144_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_54_2 i) (Q2.hfix144_54_2 i) _)
      colCert_144_54_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T144_54
      hfix144_54 hinj144_54 hcardT144_54
      (fun i => conj_mem_of_fixedPoints _ _ (T144_54 i) (hfix144_54 i) _)
      ⟨144, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T144_54_2 Q2.hfix144_54_2 Q2.hinj144_54_2
      Q2.hcardT144_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_54_2 i) (Q2.hfix144_54_2 i) _)
      colCert_144_54_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T144_54
      hfix144_54 hinj144_54 hcardT144_54
      (fun i => conj_mem_of_fixedPoints _ _ (T144_54 i) (hfix144_54 i) _)
      ⟨144, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T144_54_2 Q2.hfix144_54_2 Q2.hinj144_54_2
      Q2.hcardT144_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_54_2 i) (Q2.hfix144_54_2 i) _)
      colCert_144_54_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T144_54
      hfix144_54 hinj144_54 hcardT144_54
      (fun i => conj_mem_of_fixedPoints _ _ (T144_54 i) (hfix144_54 i) _)
      ⟨144, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T144_54_2 Q2.hfix144_54_2 Q2.hinj144_54_2
      Q2.hcardT144_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_54_2 i) (Q2.hfix144_54_2 i) _)
      colCert_144_54_5.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T144_54
      hfix144_54 hinj144_54 hcardT144_54
      (fun i => conj_mem_of_fixedPoints _ _ (T144_54 i) (hfix144_54 i) _)
      ⟨144, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T144_54_2 Q2.hfix144_54_2 Q2.hinj144_54_2
      Q2.hcardT144_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_54_2 i) (Q2.hfix144_54_2 i) _)
      colCert_144_54_10.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T144_54
      hfix144_54 hinj144_54 hcardT144_54
      (fun i => conj_mem_of_fixedPoints _ _ (T144_54 i) (hfix144_54 i) _)
      ⟨144, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T144_54_2 Q2.hfix144_54_2 Q2.hinj144_54_2
      Q2.hcardT144_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_54_2 i) (Q2.hfix144_54_2 i) _)
      colCert_144_54_15.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T144_54
      hfix144_54 hinj144_54 hcardT144_54
      (fun i => conj_mem_of_fixedPoints _ _ (T144_54 i) (hfix144_54 i) _)
      ⟨144, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T144_54_2 Q2.hfix144_54_2 Q2.hinj144_54_2
      Q2.hcardT144_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_54_2 i) (Q2.hfix144_54_2 i) _)
      colCert_144_54_20.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_100_0 (hp : 0 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 0 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      colCert_144_100_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_100_1 (hp : 1 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 1 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      colCert_144_100_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_100_2 (hp : 2 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 2 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      colCert_144_100_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_100_3 (hp : 3 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 3 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      colCert_144_100_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_100_4 (hp : 4 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 4 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      colCert_144_100_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_100_5 (hp : 5 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 5 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      colCert_144_100_5.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_100_10 (hp : 10 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 10 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      colCert_144_100_10.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_100_15 (hp : 15 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 15 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      colCert_144_100_15.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_100_20 (hp : 20 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 20 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      colCert_144_100_20.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_100_25 (hp : 25 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 25 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 25 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T144_100 = colFn colCertDiv_144_100_25.D1 (m := 5) from colCertDiv_144_100_25.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 25 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T144_100_2 = colFn colCertDiv_144_100_25.D2 (m := 5) from colCertDiv_144_100_25.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_100_25_match


theorem leaf_144_100_50 (hp : 50 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 50 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 50 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T144_100 = colFn colCertDiv_144_100_50.D1 (m := 5) from colCertDiv_144_100_50.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 50 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T144_100_2 = colFn colCertDiv_144_100_50.D2 (m := 5) from colCertDiv_144_100_50.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_100_50_match


theorem leaf_144_100_75 (hp : 75 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 75 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 75 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T144_100 = colFn colCertDiv_144_100_75.D1 (m := 5) from colCertDiv_144_100_75.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 75 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T144_100_2 = colFn colCertDiv_144_100_75.D2 (m := 5) from colCertDiv_144_100_75.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_100_75_match


theorem leaf_144_100_100 (hp : 100 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 100 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp)) T144_100
      hfix144_100 hinj144_100 hcardT144_100
      (fun i => conj_mem_of_fixedPoints _ _ (T144_100 i) (hfix144_100 i) _)
      ⟨144, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 100 hp) Q2.T144_100_2 Q2.hfix144_100_2 Q2.hinj144_100_2
      Q2.hcardT144_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_100_2 i) (Q2.hfix144_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T144_100 = colFn colCertDiv_144_100_100.D1 (m := 5) from colCertDiv_144_100_100.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 100 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T144_100_2 = colFn colCertDiv_144_100_100.D2 (m := 5) from colCertDiv_144_100_100.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_100_100_match


theorem leaf_144_101_0 (hp : 0 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp)) T144_101
      hfix144_101 hinj144_101 hcardT144_101
      (fun i => conj_mem_of_fixedPoints _ _ (T144_101 i) (hfix144_101 i) _)
      ⟨144, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 0 hp) Q2.T144_101_2 Q2.hfix144_101_2 Q2.hinj144_101_2
      Q2.hcardT144_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_101_2 i) (Q2.hfix144_101_2 i) _)
      colCert_144_101_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_101_1 (hp : 1 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp)) T144_101
      hfix144_101 hinj144_101 hcardT144_101
      (fun i => conj_mem_of_fixedPoints _ _ (T144_101 i) (hfix144_101 i) _)
      ⟨144, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 1 hp) Q2.T144_101_2 Q2.hfix144_101_2 Q2.hinj144_101_2
      Q2.hcardT144_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_101_2 i) (Q2.hfix144_101_2 i) _)
      colCert_144_101_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_101_2 (hp : 2 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp)) T144_101
      hfix144_101 hinj144_101 hcardT144_101
      (fun i => conj_mem_of_fixedPoints _ _ (T144_101 i) (hfix144_101 i) _)
      ⟨144, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 2 hp) Q2.T144_101_2 Q2.hfix144_101_2 Q2.hinj144_101_2
      Q2.hcardT144_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_101_2 i) (Q2.hfix144_101_2 i) _)
      colCert_144_101_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_101_3 (hp : 3 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp)) T144_101
      hfix144_101 hinj144_101 hcardT144_101
      (fun i => conj_mem_of_fixedPoints _ _ (T144_101 i) (hfix144_101 i) _)
      ⟨144, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 3 hp) Q2.T144_101_2 Q2.hfix144_101_2 Q2.hinj144_101_2
      Q2.hcardT144_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_101_2 i) (Q2.hfix144_101_2 i) _)
      colCert_144_101_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_101_4 (hp : 4 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp)) T144_101
      hfix144_101 hinj144_101 hcardT144_101
      (fun i => conj_mem_of_fixedPoints _ _ (T144_101 i) (hfix144_101 i) _)
      ⟨144, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 4 hp) Q2.T144_101_2 Q2.hfix144_101_2 Q2.hinj144_101_2
      Q2.hcardT144_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_101_2 i) (Q2.hfix144_101_2 i) _)
      colCert_144_101_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_101_5 (hp : 5 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp)) T144_101
      hfix144_101 hinj144_101 hcardT144_101
      (fun i => conj_mem_of_fixedPoints _ _ (T144_101 i) (hfix144_101 i) _)
      ⟨144, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 5 hp) Q2.T144_101_2 Q2.hfix144_101_2 Q2.hinj144_101_2
      Q2.hcardT144_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_101_2 i) (Q2.hfix144_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T144_101 = colFn colCertDiv_144_101_5.D1 (m := 5) from colCertDiv_144_101_5.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 5 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T144_101_2 = colFn colCertDiv_144_101_5.D2 (m := 5) from colCertDiv_144_101_5.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_101_5_match


theorem leaf_144_101_10 (hp : 10 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp)) T144_101
      hfix144_101 hinj144_101 hcardT144_101
      (fun i => conj_mem_of_fixedPoints _ _ (T144_101 i) (hfix144_101 i) _)
      ⟨144, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 10 hp) Q2.T144_101_2 Q2.hfix144_101_2 Q2.hinj144_101_2
      Q2.hcardT144_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_101_2 i) (Q2.hfix144_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T144_101 = colFn colCertDiv_144_101_10.D1 (m := 5) from colCertDiv_144_101_10.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 10 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T144_101_2 = colFn colCertDiv_144_101_10.D2 (m := 5) from colCertDiv_144_101_10.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_101_10_match


theorem leaf_144_101_15 (hp : 15 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp)) T144_101
      hfix144_101 hinj144_101 hcardT144_101
      (fun i => conj_mem_of_fixedPoints _ _ (T144_101 i) (hfix144_101 i) _)
      ⟨144, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 15 hp) Q2.T144_101_2 Q2.hfix144_101_2 Q2.hinj144_101_2
      Q2.hcardT144_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_101_2 i) (Q2.hfix144_101_2 i) _)
      colCert_144_101_15.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_101_20 (hp : 20 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp)) T144_101
      hfix144_101 hinj144_101 hcardT144_101
      (fun i => conj_mem_of_fixedPoints _ _ (T144_101 i) (hfix144_101 i) _)
      ⟨144, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 20 hp) Q2.T144_101_2 Q2.hfix144_101_2 Q2.hinj144_101_2
      Q2.hcardT144_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_101_2 i) (Q2.hfix144_101_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp) : ↥(reps ⟨101, by decide⟩)) : Coordinate 1)
        T144_101 = colFn colCertDiv_144_101_20.D1 (m := 5) from colCertDiv_144_101_20.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨101, by decide⟩ 20 hp : ↥(Q2.reps ⟨101, by decide⟩)) : Coordinate 2)
        Q2.T144_101_2 = colFn colCertDiv_144_101_20.D2 (m := 5) from colCertDiv_144_101_20.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_101_20_match


theorem leaf_144_102_0 (hp : 0 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp)) T144_102
      hfix144_102 hinj144_102 hcardT144_102
      (fun i => conj_mem_of_fixedPoints _ _ (T144_102 i) (hfix144_102 i) _)
      ⟨144, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 0 hp) Q2.T144_102_2 Q2.hfix144_102_2 Q2.hinj144_102_2
      Q2.hcardT144_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_102_2 i) (Q2.hfix144_102_2 i) _)
      colCert_144_102_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_102_1 (hp : 1 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp)) T144_102
      hfix144_102 hinj144_102 hcardT144_102
      (fun i => conj_mem_of_fixedPoints _ _ (T144_102 i) (hfix144_102 i) _)
      ⟨144, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 1 hp) Q2.T144_102_2 Q2.hfix144_102_2 Q2.hinj144_102_2
      Q2.hcardT144_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_102_2 i) (Q2.hfix144_102_2 i) _)
      colCert_144_102_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_102_2 (hp : 2 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp)) T144_102
      hfix144_102 hinj144_102 hcardT144_102
      (fun i => conj_mem_of_fixedPoints _ _ (T144_102 i) (hfix144_102 i) _)
      ⟨144, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 2 hp) Q2.T144_102_2 Q2.hfix144_102_2 Q2.hinj144_102_2
      Q2.hcardT144_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_102_2 i) (Q2.hfix144_102_2 i) _)
      colCert_144_102_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_102_3 (hp : 3 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp)) T144_102
      hfix144_102 hinj144_102 hcardT144_102
      (fun i => conj_mem_of_fixedPoints _ _ (T144_102 i) (hfix144_102 i) _)
      ⟨144, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 3 hp) Q2.T144_102_2 Q2.hfix144_102_2 Q2.hinj144_102_2
      Q2.hcardT144_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_102_2 i) (Q2.hfix144_102_2 i) _)
      colCert_144_102_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_102_4 (hp : 4 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp)) T144_102
      hfix144_102 hinj144_102 hcardT144_102
      (fun i => conj_mem_of_fixedPoints _ _ (T144_102 i) (hfix144_102 i) _)
      ⟨144, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 4 hp) Q2.T144_102_2 Q2.hfix144_102_2 Q2.hinj144_102_2
      Q2.hcardT144_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_102_2 i) (Q2.hfix144_102_2 i) _)
      colCert_144_102_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_102_5 (hp : 5 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp)) T144_102
      hfix144_102 hinj144_102 hcardT144_102
      (fun i => conj_mem_of_fixedPoints _ _ (T144_102 i) (hfix144_102 i) _)
      ⟨144, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 5 hp) Q2.T144_102_2 Q2.hfix144_102_2 Q2.hinj144_102_2
      Q2.hcardT144_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_102_2 i) (Q2.hfix144_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T144_102 = colFn colCertDiv_144_102_5.D1 (m := 5) from colCertDiv_144_102_5.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 5 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T144_102_2 = colFn colCertDiv_144_102_5.D2 (m := 5) from colCertDiv_144_102_5.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_102_5_match


theorem leaf_144_102_10 (hp : 10 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp)) T144_102
      hfix144_102 hinj144_102 hcardT144_102
      (fun i => conj_mem_of_fixedPoints _ _ (T144_102 i) (hfix144_102 i) _)
      ⟨144, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 10 hp) Q2.T144_102_2 Q2.hfix144_102_2 Q2.hinj144_102_2
      Q2.hcardT144_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_102_2 i) (Q2.hfix144_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T144_102 = colFn colCertDiv_144_102_10.D1 (m := 5) from colCertDiv_144_102_10.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 10 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T144_102_2 = colFn colCertDiv_144_102_10.D2 (m := 5) from colCertDiv_144_102_10.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_102_10_match


theorem leaf_144_102_15 (hp : 15 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp)) T144_102
      hfix144_102 hinj144_102 hcardT144_102
      (fun i => conj_mem_of_fixedPoints _ _ (T144_102 i) (hfix144_102 i) _)
      ⟨144, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 15 hp) Q2.T144_102_2 Q2.hfix144_102_2 Q2.hinj144_102_2
      Q2.hcardT144_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_102_2 i) (Q2.hfix144_102_2 i) _)
      colCert_144_102_15.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_102_20 (hp : 20 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp)) T144_102
      hfix144_102 hinj144_102 hcardT144_102
      (fun i => conj_mem_of_fixedPoints _ _ (T144_102 i) (hfix144_102 i) _)
      ⟨144, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 20 hp) Q2.T144_102_2 Q2.hfix144_102_2 Q2.hinj144_102_2
      Q2.hcardT144_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_102_2 i) (Q2.hfix144_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T144_102 = colFn colCertDiv_144_102_20.D1 (m := 5) from colCertDiv_144_102_20.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 20 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T144_102_2 = colFn colCertDiv_144_102_20.D2 (m := 5) from colCertDiv_144_102_20.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_102_20_match


theorem leaf_144_103_0 (hp : 0 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp)) T144_103
      hfix144_103 hinj144_103 hcardT144_103
      (fun i => conj_mem_of_fixedPoints _ _ (T144_103 i) (hfix144_103 i) _)
      ⟨144, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 0 hp) Q2.T144_103_2 Q2.hfix144_103_2 Q2.hinj144_103_2
      Q2.hcardT144_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_103_2 i) (Q2.hfix144_103_2 i) _)
      colCert_144_103_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_103_1 (hp : 1 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp)) T144_103
      hfix144_103 hinj144_103 hcardT144_103
      (fun i => conj_mem_of_fixedPoints _ _ (T144_103 i) (hfix144_103 i) _)
      ⟨144, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 1 hp) Q2.T144_103_2 Q2.hfix144_103_2 Q2.hinj144_103_2
      Q2.hcardT144_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_103_2 i) (Q2.hfix144_103_2 i) _)
      colCert_144_103_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_103_2 (hp : 2 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp)) T144_103
      hfix144_103 hinj144_103 hcardT144_103
      (fun i => conj_mem_of_fixedPoints _ _ (T144_103 i) (hfix144_103 i) _)
      ⟨144, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 2 hp) Q2.T144_103_2 Q2.hfix144_103_2 Q2.hinj144_103_2
      Q2.hcardT144_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_103_2 i) (Q2.hfix144_103_2 i) _)
      colCert_144_103_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_103_3 (hp : 3 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp)) T144_103
      hfix144_103 hinj144_103 hcardT144_103
      (fun i => conj_mem_of_fixedPoints _ _ (T144_103 i) (hfix144_103 i) _)
      ⟨144, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 3 hp) Q2.T144_103_2 Q2.hfix144_103_2 Q2.hinj144_103_2
      Q2.hcardT144_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_103_2 i) (Q2.hfix144_103_2 i) _)
      colCert_144_103_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_103_4 (hp : 4 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp)) T144_103
      hfix144_103 hinj144_103 hcardT144_103
      (fun i => conj_mem_of_fixedPoints _ _ (T144_103 i) (hfix144_103 i) _)
      ⟨144, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 4 hp) Q2.T144_103_2 Q2.hfix144_103_2 Q2.hinj144_103_2
      Q2.hcardT144_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_103_2 i) (Q2.hfix144_103_2 i) _)
      colCert_144_103_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_103_5 (hp : 5 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp)) T144_103
      hfix144_103 hinj144_103 hcardT144_103
      (fun i => conj_mem_of_fixedPoints _ _ (T144_103 i) (hfix144_103 i) _)
      ⟨144, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 5 hp) Q2.T144_103_2 Q2.hfix144_103_2 Q2.hinj144_103_2
      Q2.hcardT144_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_103_2 i) (Q2.hfix144_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T144_103 = colFn colCertDiv_144_103_5.D1 (m := 5) from colCertDiv_144_103_5.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 5 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T144_103_2 = colFn colCertDiv_144_103_5.D2 (m := 5) from colCertDiv_144_103_5.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_103_5_match


theorem leaf_144_103_10 (hp : 10 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp)) T144_103
      hfix144_103 hinj144_103 hcardT144_103
      (fun i => conj_mem_of_fixedPoints _ _ (T144_103 i) (hfix144_103 i) _)
      ⟨144, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 10 hp) Q2.T144_103_2 Q2.hfix144_103_2 Q2.hinj144_103_2
      Q2.hcardT144_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_103_2 i) (Q2.hfix144_103_2 i) _)
      colCert_144_103_10.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_103_15 (hp : 15 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp)) T144_103
      hfix144_103 hinj144_103 hcardT144_103
      (fun i => conj_mem_of_fixedPoints _ _ (T144_103 i) (hfix144_103 i) _)
      ⟨144, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 15 hp) Q2.T144_103_2 Q2.hfix144_103_2 Q2.hinj144_103_2
      Q2.hcardT144_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_103_2 i) (Q2.hfix144_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T144_103 = colFn colCertDiv_144_103_15.D1 (m := 5) from colCertDiv_144_103_15.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 15 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T144_103_2 = colFn colCertDiv_144_103_15.D2 (m := 5) from colCertDiv_144_103_15.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_103_15_match


theorem leaf_144_103_20 (hp : 20 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp)) T144_103
      hfix144_103 hinj144_103 hcardT144_103
      (fun i => conj_mem_of_fixedPoints _ _ (T144_103 i) (hfix144_103 i) _)
      ⟨144, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 20 hp) Q2.T144_103_2 Q2.hfix144_103_2 Q2.hinj144_103_2
      Q2.hcardT144_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_103_2 i) (Q2.hfix144_103_2 i) _)
      colCert_144_103_20.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_104_0 (hp : 0 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp)) T144_104
      hfix144_104 hinj144_104 hcardT144_104
      (fun i => conj_mem_of_fixedPoints _ _ (T144_104 i) (hfix144_104 i) _)
      ⟨144, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 0 hp) Q2.T144_104_2 Q2.hfix144_104_2 Q2.hinj144_104_2
      Q2.hcardT144_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_104_2 i) (Q2.hfix144_104_2 i) _)
      colCert_144_104_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_104_1 (hp : 1 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp)) T144_104
      hfix144_104 hinj144_104 hcardT144_104
      (fun i => conj_mem_of_fixedPoints _ _ (T144_104 i) (hfix144_104 i) _)
      ⟨144, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 1 hp) Q2.T144_104_2 Q2.hfix144_104_2 Q2.hinj144_104_2
      Q2.hcardT144_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_104_2 i) (Q2.hfix144_104_2 i) _)
      colCert_144_104_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_104_2 (hp : 2 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp)) T144_104
      hfix144_104 hinj144_104 hcardT144_104
      (fun i => conj_mem_of_fixedPoints _ _ (T144_104 i) (hfix144_104 i) _)
      ⟨144, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 2 hp) Q2.T144_104_2 Q2.hfix144_104_2 Q2.hinj144_104_2
      Q2.hcardT144_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_104_2 i) (Q2.hfix144_104_2 i) _)
      colCert_144_104_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_104_3 (hp : 3 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp)) T144_104
      hfix144_104 hinj144_104 hcardT144_104
      (fun i => conj_mem_of_fixedPoints _ _ (T144_104 i) (hfix144_104 i) _)
      ⟨144, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 3 hp) Q2.T144_104_2 Q2.hfix144_104_2 Q2.hinj144_104_2
      Q2.hcardT144_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_104_2 i) (Q2.hfix144_104_2 i) _)
      colCert_144_104_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_104_4 (hp : 4 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp)) T144_104
      hfix144_104 hinj144_104 hcardT144_104
      (fun i => conj_mem_of_fixedPoints _ _ (T144_104 i) (hfix144_104 i) _)
      ⟨144, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 4 hp) Q2.T144_104_2 Q2.hfix144_104_2 Q2.hinj144_104_2
      Q2.hcardT144_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_104_2 i) (Q2.hfix144_104_2 i) _)
      colCert_144_104_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_104_5 (hp : 5 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp)) T144_104
      hfix144_104 hinj144_104 hcardT144_104
      (fun i => conj_mem_of_fixedPoints _ _ (T144_104 i) (hfix144_104 i) _)
      ⟨144, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 5 hp) Q2.T144_104_2 Q2.hfix144_104_2 Q2.hinj144_104_2
      Q2.hcardT144_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_104_2 i) (Q2.hfix144_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T144_104 = colFn colCertDiv_144_104_5.D1 (m := 5) from colCertDiv_144_104_5.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 5 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T144_104_2 = colFn colCertDiv_144_104_5.D2 (m := 5) from colCertDiv_144_104_5.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_104_5_match


theorem leaf_144_104_10 (hp : 10 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp)) T144_104
      hfix144_104 hinj144_104 hcardT144_104
      (fun i => conj_mem_of_fixedPoints _ _ (T144_104 i) (hfix144_104 i) _)
      ⟨144, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 10 hp) Q2.T144_104_2 Q2.hfix144_104_2 Q2.hinj144_104_2
      Q2.hcardT144_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_104_2 i) (Q2.hfix144_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T144_104 = colFn colCertDiv_144_104_10.D1 (m := 5) from colCertDiv_144_104_10.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 10 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T144_104_2 = colFn colCertDiv_144_104_10.D2 (m := 5) from colCertDiv_144_104_10.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_104_10_match


theorem leaf_144_104_15 (hp : 15 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp)) T144_104
      hfix144_104 hinj144_104 hcardT144_104
      (fun i => conj_mem_of_fixedPoints _ _ (T144_104 i) (hfix144_104 i) _)
      ⟨144, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 15 hp) Q2.T144_104_2 Q2.hfix144_104_2 Q2.hinj144_104_2
      Q2.hcardT144_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_104_2 i) (Q2.hfix144_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T144_104 = colFn colCertDiv_144_104_15.D1 (m := 5) from colCertDiv_144_104_15.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 15 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T144_104_2 = colFn colCertDiv_144_104_15.D2 (m := 5) from colCertDiv_144_104_15.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_104_15_match


theorem leaf_144_104_20 (hp : 20 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨144, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp)) T144_104
      hfix144_104 hinj144_104 hcardT144_104
      (fun i => conj_mem_of_fixedPoints _ _ (T144_104 i) (hfix144_104 i) _)
      ⟨144, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 20 hp) Q2.T144_104_2 Q2.hfix144_104_2 Q2.hinj144_104_2
      Q2.hcardT144_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_104_2 i) (Q2.hfix144_104_2 i) _)
      ?_).symm
  rw [show colData1 (⟨144, by decide⟩ : Fin 148)
        ((colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp) : ↥(reps ⟨104, by decide⟩)) : Coordinate 1)
        T144_104 = colFn colCertDiv_144_104_20.D1 (m := 5) from colCertDiv_144_104_20.bind1,
    show colData2 (⟨144, by decide⟩ : Fin 148)
        ((colE2 ⟨104, by decide⟩ 20 hp : ↥(Q2.reps ⟨104, by decide⟩)) : Coordinate 2)
        Q2.T144_104_2 = colFn colCertDiv_144_104_20.D2 (m := 5) from colCertDiv_144_104_20.bind2]
  rw [alnId_144 j hj]
  exact fastcode_of_div ⟨144, by decide⟩ _ _ _
    ((alnId_144 j hj) ▸ Q2.listedAt (⟨144, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨144, by decide⟩ : Fin 148) hj hq).1) colCertDiv_144_104_20_match


theorem leaf_144_115_0 (hp : 0 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 0 (transLenTr ⟨115, by decide⟩ 0 hp)) T144_115
      hfix144_115 hinj144_115 hcardT144_115
      (fun i => conj_mem_of_fixedPoints _ _ (T144_115 i) (hfix144_115 i) _)
      ⟨144, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 0 hp) Q2.T144_115_2 Q2.hfix144_115_2 Q2.hinj144_115_2
      Q2.hcardT144_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_115_2 i) (Q2.hfix144_115_2 i) _)
      colCert_144_115_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_115_1 (hp : 1 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 1 (transLenTr ⟨115, by decide⟩ 1 hp)) T144_115
      hfix144_115 hinj144_115 hcardT144_115
      (fun i => conj_mem_of_fixedPoints _ _ (T144_115 i) (hfix144_115 i) _)
      ⟨144, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 1 hp) Q2.T144_115_2 Q2.hfix144_115_2 Q2.hinj144_115_2
      Q2.hcardT144_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_115_2 i) (Q2.hfix144_115_2 i) _)
      colCert_144_115_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_115_2 (hp : 2 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 2 (transLenTr ⟨115, by decide⟩ 2 hp)) T144_115
      hfix144_115 hinj144_115 hcardT144_115
      (fun i => conj_mem_of_fixedPoints _ _ (T144_115 i) (hfix144_115 i) _)
      ⟨144, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 2 hp) Q2.T144_115_2 Q2.hfix144_115_2 Q2.hinj144_115_2
      Q2.hcardT144_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_115_2 i) (Q2.hfix144_115_2 i) _)
      colCert_144_115_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_115_3 (hp : 3 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 3 (transLenTr ⟨115, by decide⟩ 3 hp)) T144_115
      hfix144_115 hinj144_115 hcardT144_115
      (fun i => conj_mem_of_fixedPoints _ _ (T144_115 i) (hfix144_115 i) _)
      ⟨144, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 3 hp) Q2.T144_115_2 Q2.hfix144_115_2 Q2.hinj144_115_2
      Q2.hcardT144_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_115_2 i) (Q2.hfix144_115_2 i) _)
      colCert_144_115_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_115_4 (hp : 4 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 4 (transLenTr ⟨115, by decide⟩ 4 hp)) T144_115
      hfix144_115 hinj144_115 hcardT144_115
      (fun i => conj_mem_of_fixedPoints _ _ (T144_115 i) (hfix144_115 i) _)
      ⟨144, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 4 hp) Q2.T144_115_2 Q2.hfix144_115_2 Q2.hinj144_115_2
      Q2.hcardT144_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_115_2 i) (Q2.hfix144_115_2 i) _)
      colCert_144_115_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_115_5 (hp : 5 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 5 (transLenTr ⟨115, by decide⟩ 5 hp)) T144_115
      hfix144_115 hinj144_115 hcardT144_115
      (fun i => conj_mem_of_fixedPoints _ _ (T144_115 i) (hfix144_115 i) _)
      ⟨144, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 5 hp) Q2.T144_115_2 Q2.hfix144_115_2 Q2.hinj144_115_2
      Q2.hcardT144_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_115_2 i) (Q2.hfix144_115_2 i) _)
      colCert_144_115_5.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_115_10 (hp : 10 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 10 (transLenTr ⟨115, by decide⟩ 10 hp)) T144_115
      hfix144_115 hinj144_115 hcardT144_115
      (fun i => conj_mem_of_fixedPoints _ _ (T144_115 i) (hfix144_115 i) _)
      ⟨144, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 10 hp) Q2.T144_115_2 Q2.hfix144_115_2 Q2.hinj144_115_2
      Q2.hcardT144_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_115_2 i) (Q2.hfix144_115_2 i) _)
      colCert_144_115_10.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_115_15 (hp : 15 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 15 (transLenTr ⟨115, by decide⟩ 15 hp)) T144_115
      hfix144_115 hinj144_115 hcardT144_115
      (fun i => conj_mem_of_fixedPoints _ _ (T144_115 i) (hfix144_115 i) _)
      ⟨144, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 15 hp) Q2.T144_115_2 Q2.hfix144_115_2 Q2.hinj144_115_2
      Q2.hcardT144_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_115_2 i) (Q2.hfix144_115_2 i) _)
      colCert_144_115_15.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_115_20 (hp : 20 < (Q2.transData.getD 115 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨115, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨115, by decide⟩ 20 (transLenTr ⟨115, by decide⟩ 20 hp)) T144_115
      hfix144_115 hinj144_115 hcardT144_115
      (fun i => conj_mem_of_fixedPoints _ _ (T144_115 i) (hfix144_115 i) _)
      ⟨144, by decide⟩ ⟨115, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨115, by decide⟩ 20 hp) Q2.T144_115_2 Q2.hfix144_115_2 Q2.hinj144_115_2
      Q2.hcardT144_115_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_115_2 i) (Q2.hfix144_115_2 i) _)
      colCert_144_115_20.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_0 (hp : 0 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 0 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 0 (transLenTr ⟨144, by decide⟩ 0 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 0 (transLenTr ⟨144, by decide⟩ 0 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 0 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_0.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_1 (hp : 1 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 1 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 1 (transLenTr ⟨144, by decide⟩ 1 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 1 (transLenTr ⟨144, by decide⟩ 1 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 1 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_1.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_2 (hp : 2 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 2 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 2 (transLenTr ⟨144, by decide⟩ 2 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 2 (transLenTr ⟨144, by decide⟩ 2 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 2 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_2.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_3 (hp : 3 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 3 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 3 (transLenTr ⟨144, by decide⟩ 3 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 3 (transLenTr ⟨144, by decide⟩ 3 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 3 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_3.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_4 (hp : 4 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 4 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 4 (transLenTr ⟨144, by decide⟩ 4 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 4 (transLenTr ⟨144, by decide⟩ 4 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 4 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_4.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_5 (hp : 5 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 5 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 5 (transLenTr ⟨144, by decide⟩ 5 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 5 (transLenTr ⟨144, by decide⟩ 5 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 5 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_5.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_6 (hp : 6 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 6 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 6 (transLenTr ⟨144, by decide⟩ 6 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 6 (transLenTr ⟨144, by decide⟩ 6 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 6 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_6.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_7 (hp : 7 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 7 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 7 (transLenTr ⟨144, by decide⟩ 7 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 7 (transLenTr ⟨144, by decide⟩ 7 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 7 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_7.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_8 (hp : 8 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 8 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 8 (transLenTr ⟨144, by decide⟩ 8 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 8 (transLenTr ⟨144, by decide⟩ 8 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 8 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_8.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_9 (hp : 9 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 9 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 9 (transLenTr ⟨144, by decide⟩ 9 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 9 (transLenTr ⟨144, by decide⟩ 9 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 9 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_9.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_10 (hp : 10 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 10 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 10 (transLenTr ⟨144, by decide⟩ 10 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 10 (transLenTr ⟨144, by decide⟩ 10 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 10 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_10.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_11 (hp : 11 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 11 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 11 (transLenTr ⟨144, by decide⟩ 11 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 11 (transLenTr ⟨144, by decide⟩ 11 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 11 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_11.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_12 (hp : 12 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 12 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 12 (transLenTr ⟨144, by decide⟩ 12 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 12 (transLenTr ⟨144, by decide⟩ 12 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 12 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_12.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_13 (hp : 13 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 13 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 13 (transLenTr ⟨144, by decide⟩ 13 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 13 (transLenTr ⟨144, by decide⟩ 13 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 13 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_13.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_14 (hp : 14 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 14 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 14 (transLenTr ⟨144, by decide⟩ 14 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 14 (transLenTr ⟨144, by decide⟩ 14 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 14 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_14.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_15 (hp : 15 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 15 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 15 (transLenTr ⟨144, by decide⟩ 15 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 15 (transLenTr ⟨144, by decide⟩ 15 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 15 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_15.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_16 (hp : 16 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 16 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 16 (transLenTr ⟨144, by decide⟩ 16 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 16 (transLenTr ⟨144, by decide⟩ 16 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 16 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_16.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_17 (hp : 17 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 17 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 17 (transLenTr ⟨144, by decide⟩ 17 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 17 (transLenTr ⟨144, by decide⟩ 17 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 17 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_17.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_18 (hp : 18 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 18 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 18 (transLenTr ⟨144, by decide⟩ 18 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 18 (transLenTr ⟨144, by decide⟩ 18 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 18 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_18.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_19 (hp : 19 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 19 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 19 (transLenTr ⟨144, by decide⟩ 19 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 19 (transLenTr ⟨144, by decide⟩ 19 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 19 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_19.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_20 (hp : 20 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 20 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 20 (transLenTr ⟨144, by decide⟩ 20 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 20 (transLenTr ⟨144, by decide⟩ 20 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 20 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_20.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_21 (hp : 21 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 21 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 21 (transLenTr ⟨144, by decide⟩ 21 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 21 (transLenTr ⟨144, by decide⟩ 21 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 21 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_21.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_22 (hp : 22 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 22 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 22 (transLenTr ⟨144, by decide⟩ 22 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 22 (transLenTr ⟨144, by decide⟩ 22 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 22 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_22.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_23 (hp : 23 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 23 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 23 (transLenTr ⟨144, by decide⟩ 23 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 23 (transLenTr ⟨144, by decide⟩ 23 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 23 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_23.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_144_144_24 (hp : 24 < (Q2.transData.getD 144 []).length)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ 24 hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ 24 (transLenTr ⟨144, by decide⟩ 24 hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨144, by decide⟩ : Fin 148) ⟨144, by decide⟩ _
      (validAt ⟨144, by decide⟩ (listedAt ⟨144, by decide⟩ hj))
      (colE1 ⟨144, by decide⟩ 24 (transLenTr ⟨144, by decide⟩ 24 hp)) T144_144
      hfix144_144 hinj144_144 hcardT144_144
      (fun i => conj_mem_of_fixedPoints _ _ (T144_144 i) (hfix144_144 i) _)
      ⟨144, by decide⟩ ⟨144, by decide⟩ _
      (Q2.validAt ⟨144, by decide⟩ (Q2.listedAt ⟨144, by decide⟩
        (alnCheck_rep ⟨144, by decide⟩ hj hq).1))
      (colE2 ⟨144, by decide⟩ 24 hp) Q2.T144_144_2 Q2.hfix144_144_2 Q2.hinj144_144_2
      Q2.hcardT144_144_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T144_144_2 i) (Q2.hfix144_144_2 i) _)
      colCert_144_144_24.hD ?_).symm
  rw [alnId_144 j hj]


theorem leaf_145_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T145_10
      hfix145_10 hinj145_10 hcardT145_10
      (fun i => conj_mem_of_fixedPoints _ _ (T145_10 i) (hfix145_10 i) _)
      ⟨145, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T145_10_2 Q2.hfix145_10_2 Q2.hinj145_10_2
      Q2.hcardT145_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_10_2 i) (Q2.hfix145_10_2 i) _)
      colCert_145_10_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T145_10
      hfix145_10 hinj145_10 hcardT145_10
      (fun i => conj_mem_of_fixedPoints _ _ (T145_10 i) (hfix145_10 i) _)
      ⟨145, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T145_10_2 Q2.hfix145_10_2 Q2.hinj145_10_2
      Q2.hcardT145_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_10_2 i) (Q2.hfix145_10_2 i) _)
      colCert_145_10_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T145_10
      hfix145_10 hinj145_10 hcardT145_10
      (fun i => conj_mem_of_fixedPoints _ _ (T145_10 i) (hfix145_10 i) _)
      ⟨145, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T145_10_2 Q2.hfix145_10_2 Q2.hinj145_10_2
      Q2.hcardT145_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_10_2 i) (Q2.hfix145_10_2 i) _)
      colCert_145_10_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T145_10
      hfix145_10 hinj145_10 hcardT145_10
      (fun i => conj_mem_of_fixedPoints _ _ (T145_10 i) (hfix145_10 i) _)
      ⟨145, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T145_10_2 Q2.hfix145_10_2 Q2.hinj145_10_2
      Q2.hcardT145_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_10_2 i) (Q2.hfix145_10_2 i) _)
      colCert_145_10_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T145_10
      hfix145_10 hinj145_10 hcardT145_10
      (fun i => conj_mem_of_fixedPoints _ _ (T145_10 i) (hfix145_10 i) _)
      ⟨145, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T145_10_2 Q2.hfix145_10_2 Q2.hinj145_10_2
      Q2.hcardT145_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_10_2 i) (Q2.hfix145_10_2 i) _)
      colCert_145_10_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T145_11
      hfix145_11 hinj145_11 hcardT145_11
      (fun i => conj_mem_of_fixedPoints _ _ (T145_11 i) (hfix145_11 i) _)
      ⟨145, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T145_11_2 Q2.hfix145_11_2 Q2.hinj145_11_2
      Q2.hcardT145_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_11_2 i) (Q2.hfix145_11_2 i) _)
      colCert_145_11_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T145_11
      hfix145_11 hinj145_11 hcardT145_11
      (fun i => conj_mem_of_fixedPoints _ _ (T145_11 i) (hfix145_11 i) _)
      ⟨145, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T145_11_2 Q2.hfix145_11_2 Q2.hinj145_11_2
      Q2.hcardT145_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_11_2 i) (Q2.hfix145_11_2 i) _)
      colCert_145_11_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T145_11
      hfix145_11 hinj145_11 hcardT145_11
      (fun i => conj_mem_of_fixedPoints _ _ (T145_11 i) (hfix145_11 i) _)
      ⟨145, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T145_11_2 Q2.hfix145_11_2 Q2.hinj145_11_2
      Q2.hcardT145_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_11_2 i) (Q2.hfix145_11_2 i) _)
      colCert_145_11_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T145_11
      hfix145_11 hinj145_11 hcardT145_11
      (fun i => conj_mem_of_fixedPoints _ _ (T145_11 i) (hfix145_11 i) _)
      ⟨145, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T145_11_2 Q2.hfix145_11_2 Q2.hinj145_11_2
      Q2.hcardT145_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_11_2 i) (Q2.hfix145_11_2 i) _)
      colCert_145_11_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T145_11
      hfix145_11 hinj145_11 hcardT145_11
      (fun i => conj_mem_of_fixedPoints _ _ (T145_11 i) (hfix145_11 i) _)
      ⟨145, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T145_11_2 Q2.hfix145_11_2 Q2.hinj145_11_2
      Q2.hcardT145_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_11_2 i) (Q2.hfix145_11_2 i) _)
      colCert_145_11_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T145_12
      hfix145_12 hinj145_12 hcardT145_12
      (fun i => conj_mem_of_fixedPoints _ _ (T145_12 i) (hfix145_12 i) _)
      ⟨145, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T145_12_2 Q2.hfix145_12_2 Q2.hinj145_12_2
      Q2.hcardT145_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_12_2 i) (Q2.hfix145_12_2 i) _)
      colCert_145_12_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T145_12
      hfix145_12 hinj145_12 hcardT145_12
      (fun i => conj_mem_of_fixedPoints _ _ (T145_12 i) (hfix145_12 i) _)
      ⟨145, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T145_12_2 Q2.hfix145_12_2 Q2.hinj145_12_2
      Q2.hcardT145_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_12_2 i) (Q2.hfix145_12_2 i) _)
      colCert_145_12_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T145_12
      hfix145_12 hinj145_12 hcardT145_12
      (fun i => conj_mem_of_fixedPoints _ _ (T145_12 i) (hfix145_12 i) _)
      ⟨145, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T145_12_2 Q2.hfix145_12_2 Q2.hinj145_12_2
      Q2.hcardT145_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_12_2 i) (Q2.hfix145_12_2 i) _)
      colCert_145_12_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T145_12
      hfix145_12 hinj145_12 hcardT145_12
      (fun i => conj_mem_of_fixedPoints _ _ (T145_12 i) (hfix145_12 i) _)
      ⟨145, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T145_12_2 Q2.hfix145_12_2 Q2.hinj145_12_2
      Q2.hcardT145_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_12_2 i) (Q2.hfix145_12_2 i) _)
      colCert_145_12_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T145_12
      hfix145_12 hinj145_12 hcardT145_12
      (fun i => conj_mem_of_fixedPoints _ _ (T145_12 i) (hfix145_12 i) _)
      ⟨145, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T145_12_2 Q2.hfix145_12_2 Q2.hinj145_12_2
      Q2.hcardT145_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_12_2 i) (Q2.hfix145_12_2 i) _)
      colCert_145_12_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T145_43
      hfix145_43 hinj145_43 hcardT145_43
      (fun i => conj_mem_of_fixedPoints _ _ (T145_43 i) (hfix145_43 i) _)
      ⟨145, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T145_43_2 Q2.hfix145_43_2 Q2.hinj145_43_2
      Q2.hcardT145_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_43_2 i) (Q2.hfix145_43_2 i) _)
      colCert_145_43_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T145_43
      hfix145_43 hinj145_43 hcardT145_43
      (fun i => conj_mem_of_fixedPoints _ _ (T145_43 i) (hfix145_43 i) _)
      ⟨145, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T145_43_2 Q2.hfix145_43_2 Q2.hinj145_43_2
      Q2.hcardT145_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_43_2 i) (Q2.hfix145_43_2 i) _)
      colCert_145_43_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T145_43
      hfix145_43 hinj145_43 hcardT145_43
      (fun i => conj_mem_of_fixedPoints _ _ (T145_43 i) (hfix145_43 i) _)
      ⟨145, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T145_43_2 Q2.hfix145_43_2 Q2.hinj145_43_2
      Q2.hcardT145_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_43_2 i) (Q2.hfix145_43_2 i) _)
      colCert_145_43_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T145_43
      hfix145_43 hinj145_43 hcardT145_43
      (fun i => conj_mem_of_fixedPoints _ _ (T145_43 i) (hfix145_43 i) _)
      ⟨145, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T145_43_2 Q2.hfix145_43_2 Q2.hinj145_43_2
      Q2.hcardT145_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_43_2 i) (Q2.hfix145_43_2 i) _)
      colCert_145_43_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T145_43
      hfix145_43 hinj145_43 hcardT145_43
      (fun i => conj_mem_of_fixedPoints _ _ (T145_43 i) (hfix145_43 i) _)
      ⟨145, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T145_43_2 Q2.hfix145_43_2 Q2.hinj145_43_2
      Q2.hcardT145_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_43_2 i) (Q2.hfix145_43_2 i) _)
      colCert_145_43_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T145_43
      hfix145_43 hinj145_43 hcardT145_43
      (fun i => conj_mem_of_fixedPoints _ _ (T145_43 i) (hfix145_43 i) _)
      ⟨145, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T145_43_2 Q2.hfix145_43_2 Q2.hinj145_43_2
      Q2.hcardT145_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_43_2 i) (Q2.hfix145_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T145_43 = colFn colCertDiv_145_43_5.D1 (m := 5) from colCertDiv_145_43_5.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T145_43_2 = colFn colCertDiv_145_43_5.D2 (m := 5) from colCertDiv_145_43_5.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_43_5_match


theorem leaf_145_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T145_43
      hfix145_43 hinj145_43 hcardT145_43
      (fun i => conj_mem_of_fixedPoints _ _ (T145_43 i) (hfix145_43 i) _)
      ⟨145, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T145_43_2 Q2.hfix145_43_2 Q2.hinj145_43_2
      Q2.hcardT145_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_43_2 i) (Q2.hfix145_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T145_43 = colFn colCertDiv_145_43_10.D1 (m := 5) from colCertDiv_145_43_10.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T145_43_2 = colFn colCertDiv_145_43_10.D2 (m := 5) from colCertDiv_145_43_10.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_43_10_match


theorem leaf_145_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T145_43
      hfix145_43 hinj145_43 hcardT145_43
      (fun i => conj_mem_of_fixedPoints _ _ (T145_43 i) (hfix145_43 i) _)
      ⟨145, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T145_43_2 Q2.hfix145_43_2 Q2.hinj145_43_2
      Q2.hcardT145_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_43_2 i) (Q2.hfix145_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T145_43 = colFn colCertDiv_145_43_15.D1 (m := 5) from colCertDiv_145_43_15.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T145_43_2 = colFn colCertDiv_145_43_15.D2 (m := 5) from colCertDiv_145_43_15.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_43_15_match


theorem leaf_145_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T145_43
      hfix145_43 hinj145_43 hcardT145_43
      (fun i => conj_mem_of_fixedPoints _ _ (T145_43 i) (hfix145_43 i) _)
      ⟨145, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T145_43_2 Q2.hfix145_43_2 Q2.hinj145_43_2
      Q2.hcardT145_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_43_2 i) (Q2.hfix145_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T145_43 = colFn colCertDiv_145_43_20.D1 (m := 5) from colCertDiv_145_43_20.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T145_43_2 = colFn colCertDiv_145_43_20.D2 (m := 5) from colCertDiv_145_43_20.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_43_20_match


theorem leaf_145_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T145_44
      hfix145_44 hinj145_44 hcardT145_44
      (fun i => conj_mem_of_fixedPoints _ _ (T145_44 i) (hfix145_44 i) _)
      ⟨145, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T145_44_2 Q2.hfix145_44_2 Q2.hinj145_44_2
      Q2.hcardT145_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_44_2 i) (Q2.hfix145_44_2 i) _)
      colCert_145_44_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T145_44
      hfix145_44 hinj145_44 hcardT145_44
      (fun i => conj_mem_of_fixedPoints _ _ (T145_44 i) (hfix145_44 i) _)
      ⟨145, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T145_44_2 Q2.hfix145_44_2 Q2.hinj145_44_2
      Q2.hcardT145_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_44_2 i) (Q2.hfix145_44_2 i) _)
      colCert_145_44_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T145_44
      hfix145_44 hinj145_44 hcardT145_44
      (fun i => conj_mem_of_fixedPoints _ _ (T145_44 i) (hfix145_44 i) _)
      ⟨145, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T145_44_2 Q2.hfix145_44_2 Q2.hinj145_44_2
      Q2.hcardT145_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_44_2 i) (Q2.hfix145_44_2 i) _)
      colCert_145_44_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T145_44
      hfix145_44 hinj145_44 hcardT145_44
      (fun i => conj_mem_of_fixedPoints _ _ (T145_44 i) (hfix145_44 i) _)
      ⟨145, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T145_44_2 Q2.hfix145_44_2 Q2.hinj145_44_2
      Q2.hcardT145_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_44_2 i) (Q2.hfix145_44_2 i) _)
      colCert_145_44_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T145_44
      hfix145_44 hinj145_44 hcardT145_44
      (fun i => conj_mem_of_fixedPoints _ _ (T145_44 i) (hfix145_44 i) _)
      ⟨145, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T145_44_2 Q2.hfix145_44_2 Q2.hinj145_44_2
      Q2.hcardT145_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_44_2 i) (Q2.hfix145_44_2 i) _)
      colCert_145_44_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T145_44
      hfix145_44 hinj145_44 hcardT145_44
      (fun i => conj_mem_of_fixedPoints _ _ (T145_44 i) (hfix145_44 i) _)
      ⟨145, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T145_44_2 Q2.hfix145_44_2 Q2.hinj145_44_2
      Q2.hcardT145_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_44_2 i) (Q2.hfix145_44_2 i) _)
      colCert_145_44_5.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T145_44
      hfix145_44 hinj145_44 hcardT145_44
      (fun i => conj_mem_of_fixedPoints _ _ (T145_44 i) (hfix145_44 i) _)
      ⟨145, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T145_44_2 Q2.hfix145_44_2 Q2.hinj145_44_2
      Q2.hcardT145_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_44_2 i) (Q2.hfix145_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T145_44 = colFn colCertDiv_145_44_10.D1 (m := 5) from colCertDiv_145_44_10.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 10 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T145_44_2 = colFn colCertDiv_145_44_10.D2 (m := 5) from colCertDiv_145_44_10.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_44_10_match


theorem leaf_145_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T145_44
      hfix145_44 hinj145_44 hcardT145_44
      (fun i => conj_mem_of_fixedPoints _ _ (T145_44 i) (hfix145_44 i) _)
      ⟨145, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T145_44_2 Q2.hfix145_44_2 Q2.hinj145_44_2
      Q2.hcardT145_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_44_2 i) (Q2.hfix145_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T145_44 = colFn colCertDiv_145_44_15.D1 (m := 5) from colCertDiv_145_44_15.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 15 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T145_44_2 = colFn colCertDiv_145_44_15.D2 (m := 5) from colCertDiv_145_44_15.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_44_15_match


theorem leaf_145_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T145_44
      hfix145_44 hinj145_44 hcardT145_44
      (fun i => conj_mem_of_fixedPoints _ _ (T145_44 i) (hfix145_44 i) _)
      ⟨145, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T145_44_2 Q2.hfix145_44_2 Q2.hinj145_44_2
      Q2.hcardT145_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_44_2 i) (Q2.hfix145_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T145_44 = colFn colCertDiv_145_44_20.D1 (m := 5) from colCertDiv_145_44_20.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 20 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T145_44_2 = colFn colCertDiv_145_44_20.D2 (m := 5) from colCertDiv_145_44_20.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_44_20_match


theorem leaf_145_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T145_45
      hfix145_45 hinj145_45 hcardT145_45
      (fun i => conj_mem_of_fixedPoints _ _ (T145_45 i) (hfix145_45 i) _)
      ⟨145, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T145_45_2 Q2.hfix145_45_2 Q2.hinj145_45_2
      Q2.hcardT145_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_45_2 i) (Q2.hfix145_45_2 i) _)
      colCert_145_45_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T145_45
      hfix145_45 hinj145_45 hcardT145_45
      (fun i => conj_mem_of_fixedPoints _ _ (T145_45 i) (hfix145_45 i) _)
      ⟨145, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T145_45_2 Q2.hfix145_45_2 Q2.hinj145_45_2
      Q2.hcardT145_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_45_2 i) (Q2.hfix145_45_2 i) _)
      colCert_145_45_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T145_45
      hfix145_45 hinj145_45 hcardT145_45
      (fun i => conj_mem_of_fixedPoints _ _ (T145_45 i) (hfix145_45 i) _)
      ⟨145, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T145_45_2 Q2.hfix145_45_2 Q2.hinj145_45_2
      Q2.hcardT145_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_45_2 i) (Q2.hfix145_45_2 i) _)
      colCert_145_45_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T145_45
      hfix145_45 hinj145_45 hcardT145_45
      (fun i => conj_mem_of_fixedPoints _ _ (T145_45 i) (hfix145_45 i) _)
      ⟨145, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T145_45_2 Q2.hfix145_45_2 Q2.hinj145_45_2
      Q2.hcardT145_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_45_2 i) (Q2.hfix145_45_2 i) _)
      colCert_145_45_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T145_45
      hfix145_45 hinj145_45 hcardT145_45
      (fun i => conj_mem_of_fixedPoints _ _ (T145_45 i) (hfix145_45 i) _)
      ⟨145, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T145_45_2 Q2.hfix145_45_2 Q2.hinj145_45_2
      Q2.hcardT145_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_45_2 i) (Q2.hfix145_45_2 i) _)
      colCert_145_45_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T145_45
      hfix145_45 hinj145_45 hcardT145_45
      (fun i => conj_mem_of_fixedPoints _ _ (T145_45 i) (hfix145_45 i) _)
      ⟨145, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T145_45_2 Q2.hfix145_45_2 Q2.hinj145_45_2
      Q2.hcardT145_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_45_2 i) (Q2.hfix145_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T145_45 = colFn colCertDiv_145_45_5.D1 (m := 5) from colCertDiv_145_45_5.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 5 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T145_45_2 = colFn colCertDiv_145_45_5.D2 (m := 5) from colCertDiv_145_45_5.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_45_5_match


theorem leaf_145_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T145_45
      hfix145_45 hinj145_45 hcardT145_45
      (fun i => conj_mem_of_fixedPoints _ _ (T145_45 i) (hfix145_45 i) _)
      ⟨145, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T145_45_2 Q2.hfix145_45_2 Q2.hinj145_45_2
      Q2.hcardT145_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_45_2 i) (Q2.hfix145_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T145_45 = colFn colCertDiv_145_45_10.D1 (m := 5) from colCertDiv_145_45_10.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 10 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T145_45_2 = colFn colCertDiv_145_45_10.D2 (m := 5) from colCertDiv_145_45_10.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_45_10_match


theorem leaf_145_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T145_45
      hfix145_45 hinj145_45 hcardT145_45
      (fun i => conj_mem_of_fixedPoints _ _ (T145_45 i) (hfix145_45 i) _)
      ⟨145, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T145_45_2 Q2.hfix145_45_2 Q2.hinj145_45_2
      Q2.hcardT145_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_45_2 i) (Q2.hfix145_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T145_45 = colFn colCertDiv_145_45_15.D1 (m := 5) from colCertDiv_145_45_15.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 15 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T145_45_2 = colFn colCertDiv_145_45_15.D2 (m := 5) from colCertDiv_145_45_15.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_45_15_match


theorem leaf_145_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T145_45
      hfix145_45 hinj145_45 hcardT145_45
      (fun i => conj_mem_of_fixedPoints _ _ (T145_45 i) (hfix145_45 i) _)
      ⟨145, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T145_45_2 Q2.hfix145_45_2 Q2.hinj145_45_2
      Q2.hcardT145_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_45_2 i) (Q2.hfix145_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T145_45 = colFn colCertDiv_145_45_20.D1 (m := 5) from colCertDiv_145_45_20.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 20 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T145_45_2 = colFn colCertDiv_145_45_20.D2 (m := 5) from colCertDiv_145_45_20.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_45_20_match


theorem leaf_145_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T145_46
      hfix145_46 hinj145_46 hcardT145_46
      (fun i => conj_mem_of_fixedPoints _ _ (T145_46 i) (hfix145_46 i) _)
      ⟨145, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T145_46_2 Q2.hfix145_46_2 Q2.hinj145_46_2
      Q2.hcardT145_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_46_2 i) (Q2.hfix145_46_2 i) _)
      colCert_145_46_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T145_46
      hfix145_46 hinj145_46 hcardT145_46
      (fun i => conj_mem_of_fixedPoints _ _ (T145_46 i) (hfix145_46 i) _)
      ⟨145, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T145_46_2 Q2.hfix145_46_2 Q2.hinj145_46_2
      Q2.hcardT145_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_46_2 i) (Q2.hfix145_46_2 i) _)
      colCert_145_46_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T145_46
      hfix145_46 hinj145_46 hcardT145_46
      (fun i => conj_mem_of_fixedPoints _ _ (T145_46 i) (hfix145_46 i) _)
      ⟨145, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T145_46_2 Q2.hfix145_46_2 Q2.hinj145_46_2
      Q2.hcardT145_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_46_2 i) (Q2.hfix145_46_2 i) _)
      colCert_145_46_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T145_46
      hfix145_46 hinj145_46 hcardT145_46
      (fun i => conj_mem_of_fixedPoints _ _ (T145_46 i) (hfix145_46 i) _)
      ⟨145, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T145_46_2 Q2.hfix145_46_2 Q2.hinj145_46_2
      Q2.hcardT145_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_46_2 i) (Q2.hfix145_46_2 i) _)
      colCert_145_46_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T145_46
      hfix145_46 hinj145_46 hcardT145_46
      (fun i => conj_mem_of_fixedPoints _ _ (T145_46 i) (hfix145_46 i) _)
      ⟨145, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T145_46_2 Q2.hfix145_46_2 Q2.hinj145_46_2
      Q2.hcardT145_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_46_2 i) (Q2.hfix145_46_2 i) _)
      colCert_145_46_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T145_46
      hfix145_46 hinj145_46 hcardT145_46
      (fun i => conj_mem_of_fixedPoints _ _ (T145_46 i) (hfix145_46 i) _)
      ⟨145, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T145_46_2 Q2.hfix145_46_2 Q2.hinj145_46_2
      Q2.hcardT145_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_46_2 i) (Q2.hfix145_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T145_46 = colFn colCertDiv_145_46_5.D1 (m := 5) from colCertDiv_145_46_5.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 5 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T145_46_2 = colFn colCertDiv_145_46_5.D2 (m := 5) from colCertDiv_145_46_5.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_46_5_match


theorem leaf_145_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T145_46
      hfix145_46 hinj145_46 hcardT145_46
      (fun i => conj_mem_of_fixedPoints _ _ (T145_46 i) (hfix145_46 i) _)
      ⟨145, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T145_46_2 Q2.hfix145_46_2 Q2.hinj145_46_2
      Q2.hcardT145_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_46_2 i) (Q2.hfix145_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T145_46 = colFn colCertDiv_145_46_10.D1 (m := 5) from colCertDiv_145_46_10.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 10 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T145_46_2 = colFn colCertDiv_145_46_10.D2 (m := 5) from colCertDiv_145_46_10.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_46_10_match


theorem leaf_145_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T145_46
      hfix145_46 hinj145_46 hcardT145_46
      (fun i => conj_mem_of_fixedPoints _ _ (T145_46 i) (hfix145_46 i) _)
      ⟨145, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T145_46_2 Q2.hfix145_46_2 Q2.hinj145_46_2
      Q2.hcardT145_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_46_2 i) (Q2.hfix145_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T145_46 = colFn colCertDiv_145_46_15.D1 (m := 5) from colCertDiv_145_46_15.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 15 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T145_46_2 = colFn colCertDiv_145_46_15.D2 (m := 5) from colCertDiv_145_46_15.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_46_15_match


theorem leaf_145_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T145_46
      hfix145_46 hinj145_46 hcardT145_46
      (fun i => conj_mem_of_fixedPoints _ _ (T145_46 i) (hfix145_46 i) _)
      ⟨145, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T145_46_2 Q2.hfix145_46_2 Q2.hinj145_46_2
      Q2.hcardT145_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_46_2 i) (Q2.hfix145_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T145_46 = colFn colCertDiv_145_46_20.D1 (m := 5) from colCertDiv_145_46_20.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 20 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T145_46_2 = colFn colCertDiv_145_46_20.D2 (m := 5) from colCertDiv_145_46_20.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_46_20_match


theorem leaf_145_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T145_47
      hfix145_47 hinj145_47 hcardT145_47
      (fun i => conj_mem_of_fixedPoints _ _ (T145_47 i) (hfix145_47 i) _)
      ⟨145, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T145_47_2 Q2.hfix145_47_2 Q2.hinj145_47_2
      Q2.hcardT145_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_47_2 i) (Q2.hfix145_47_2 i) _)
      colCert_145_47_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T145_47
      hfix145_47 hinj145_47 hcardT145_47
      (fun i => conj_mem_of_fixedPoints _ _ (T145_47 i) (hfix145_47 i) _)
      ⟨145, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T145_47_2 Q2.hfix145_47_2 Q2.hinj145_47_2
      Q2.hcardT145_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_47_2 i) (Q2.hfix145_47_2 i) _)
      colCert_145_47_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T145_47
      hfix145_47 hinj145_47 hcardT145_47
      (fun i => conj_mem_of_fixedPoints _ _ (T145_47 i) (hfix145_47 i) _)
      ⟨145, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T145_47_2 Q2.hfix145_47_2 Q2.hinj145_47_2
      Q2.hcardT145_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_47_2 i) (Q2.hfix145_47_2 i) _)
      colCert_145_47_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T145_47
      hfix145_47 hinj145_47 hcardT145_47
      (fun i => conj_mem_of_fixedPoints _ _ (T145_47 i) (hfix145_47 i) _)
      ⟨145, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T145_47_2 Q2.hfix145_47_2 Q2.hinj145_47_2
      Q2.hcardT145_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_47_2 i) (Q2.hfix145_47_2 i) _)
      colCert_145_47_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T145_47
      hfix145_47 hinj145_47 hcardT145_47
      (fun i => conj_mem_of_fixedPoints _ _ (T145_47 i) (hfix145_47 i) _)
      ⟨145, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T145_47_2 Q2.hfix145_47_2 Q2.hinj145_47_2
      Q2.hcardT145_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_47_2 i) (Q2.hfix145_47_2 i) _)
      colCert_145_47_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T145_47
      hfix145_47 hinj145_47 hcardT145_47
      (fun i => conj_mem_of_fixedPoints _ _ (T145_47 i) (hfix145_47 i) _)
      ⟨145, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T145_47_2 Q2.hfix145_47_2 Q2.hinj145_47_2
      Q2.hcardT145_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_47_2 i) (Q2.hfix145_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T145_47 = colFn colCertDiv_145_47_5.D1 (m := 5) from colCertDiv_145_47_5.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T145_47_2 = colFn colCertDiv_145_47_5.D2 (m := 5) from colCertDiv_145_47_5.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_47_5_match


theorem leaf_145_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T145_47
      hfix145_47 hinj145_47 hcardT145_47
      (fun i => conj_mem_of_fixedPoints _ _ (T145_47 i) (hfix145_47 i) _)
      ⟨145, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T145_47_2 Q2.hfix145_47_2 Q2.hinj145_47_2
      Q2.hcardT145_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_47_2 i) (Q2.hfix145_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T145_47 = colFn colCertDiv_145_47_10.D1 (m := 5) from colCertDiv_145_47_10.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T145_47_2 = colFn colCertDiv_145_47_10.D2 (m := 5) from colCertDiv_145_47_10.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_47_10_match


theorem leaf_145_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T145_47
      hfix145_47 hinj145_47 hcardT145_47
      (fun i => conj_mem_of_fixedPoints _ _ (T145_47 i) (hfix145_47 i) _)
      ⟨145, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T145_47_2 Q2.hfix145_47_2 Q2.hinj145_47_2
      Q2.hcardT145_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_47_2 i) (Q2.hfix145_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T145_47 = colFn colCertDiv_145_47_15.D1 (m := 5) from colCertDiv_145_47_15.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T145_47_2 = colFn colCertDiv_145_47_15.D2 (m := 5) from colCertDiv_145_47_15.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_47_15_match


theorem leaf_145_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨145, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T145_47
      hfix145_47 hinj145_47 hcardT145_47
      (fun i => conj_mem_of_fixedPoints _ _ (T145_47 i) (hfix145_47 i) _)
      ⟨145, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T145_47_2 Q2.hfix145_47_2 Q2.hinj145_47_2
      Q2.hcardT145_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_47_2 i) (Q2.hfix145_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨145, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T145_47 = colFn colCertDiv_145_47_20.D1 (m := 5) from colCertDiv_145_47_20.bind1,
    show colData2 (⟨145, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T145_47_2 = colFn colCertDiv_145_47_20.D2 (m := 5) from colCertDiv_145_47_20.bind2]
  rw [alnId_145 j hj]
  exact fastcode_of_div ⟨145, by decide⟩ _ _ _
    ((alnId_145 j hj) ▸ Q2.listedAt (⟨145, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨145, by decide⟩ : Fin 148) hj hq).1) colCertDiv_145_47_20_match


theorem leaf_145_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T145_53
      hfix145_53 hinj145_53 hcardT145_53
      (fun i => conj_mem_of_fixedPoints _ _ (T145_53 i) (hfix145_53 i) _)
      ⟨145, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T145_53_2 Q2.hfix145_53_2 Q2.hinj145_53_2
      Q2.hcardT145_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_53_2 i) (Q2.hfix145_53_2 i) _)
      colCert_145_53_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T145_53
      hfix145_53 hinj145_53 hcardT145_53
      (fun i => conj_mem_of_fixedPoints _ _ (T145_53 i) (hfix145_53 i) _)
      ⟨145, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T145_53_2 Q2.hfix145_53_2 Q2.hinj145_53_2
      Q2.hcardT145_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_53_2 i) (Q2.hfix145_53_2 i) _)
      colCert_145_53_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T145_53
      hfix145_53 hinj145_53 hcardT145_53
      (fun i => conj_mem_of_fixedPoints _ _ (T145_53 i) (hfix145_53 i) _)
      ⟨145, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T145_53_2 Q2.hfix145_53_2 Q2.hinj145_53_2
      Q2.hcardT145_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_53_2 i) (Q2.hfix145_53_2 i) _)
      colCert_145_53_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T145_53
      hfix145_53 hinj145_53 hcardT145_53
      (fun i => conj_mem_of_fixedPoints _ _ (T145_53 i) (hfix145_53 i) _)
      ⟨145, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T145_53_2 Q2.hfix145_53_2 Q2.hinj145_53_2
      Q2.hcardT145_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_53_2 i) (Q2.hfix145_53_2 i) _)
      colCert_145_53_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T145_53
      hfix145_53 hinj145_53 hcardT145_53
      (fun i => conj_mem_of_fixedPoints _ _ (T145_53 i) (hfix145_53 i) _)
      ⟨145, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T145_53_2 Q2.hfix145_53_2 Q2.hinj145_53_2
      Q2.hcardT145_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_53_2 i) (Q2.hfix145_53_2 i) _)
      colCert_145_53_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T145_53
      hfix145_53 hinj145_53 hcardT145_53
      (fun i => conj_mem_of_fixedPoints _ _ (T145_53 i) (hfix145_53 i) _)
      ⟨145, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T145_53_2 Q2.hfix145_53_2 Q2.hinj145_53_2
      Q2.hcardT145_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_53_2 i) (Q2.hfix145_53_2 i) _)
      colCert_145_53_5.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T145_53
      hfix145_53 hinj145_53 hcardT145_53
      (fun i => conj_mem_of_fixedPoints _ _ (T145_53 i) (hfix145_53 i) _)
      ⟨145, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T145_53_2 Q2.hfix145_53_2 Q2.hinj145_53_2
      Q2.hcardT145_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_53_2 i) (Q2.hfix145_53_2 i) _)
      colCert_145_53_10.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T145_53
      hfix145_53 hinj145_53 hcardT145_53
      (fun i => conj_mem_of_fixedPoints _ _ (T145_53 i) (hfix145_53 i) _)
      ⟨145, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T145_53_2 Q2.hfix145_53_2 Q2.hinj145_53_2
      Q2.hcardT145_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_53_2 i) (Q2.hfix145_53_2 i) _)
      colCert_145_53_15.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T145_53
      hfix145_53 hinj145_53 hcardT145_53
      (fun i => conj_mem_of_fixedPoints _ _ (T145_53 i) (hfix145_53 i) _)
      ⟨145, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T145_53_2 Q2.hfix145_53_2 Q2.hinj145_53_2
      Q2.hcardT145_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_53_2 i) (Q2.hfix145_53_2 i) _)
      colCert_145_53_20.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T145_54
      hfix145_54 hinj145_54 hcardT145_54
      (fun i => conj_mem_of_fixedPoints _ _ (T145_54 i) (hfix145_54 i) _)
      ⟨145, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T145_54_2 Q2.hfix145_54_2 Q2.hinj145_54_2
      Q2.hcardT145_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_54_2 i) (Q2.hfix145_54_2 i) _)
      colCert_145_54_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T145_54
      hfix145_54 hinj145_54 hcardT145_54
      (fun i => conj_mem_of_fixedPoints _ _ (T145_54 i) (hfix145_54 i) _)
      ⟨145, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T145_54_2 Q2.hfix145_54_2 Q2.hinj145_54_2
      Q2.hcardT145_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_54_2 i) (Q2.hfix145_54_2 i) _)
      colCert_145_54_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T145_54
      hfix145_54 hinj145_54 hcardT145_54
      (fun i => conj_mem_of_fixedPoints _ _ (T145_54 i) (hfix145_54 i) _)
      ⟨145, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T145_54_2 Q2.hfix145_54_2 Q2.hinj145_54_2
      Q2.hcardT145_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_54_2 i) (Q2.hfix145_54_2 i) _)
      colCert_145_54_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T145_54
      hfix145_54 hinj145_54 hcardT145_54
      (fun i => conj_mem_of_fixedPoints _ _ (T145_54 i) (hfix145_54 i) _)
      ⟨145, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T145_54_2 Q2.hfix145_54_2 Q2.hinj145_54_2
      Q2.hcardT145_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_54_2 i) (Q2.hfix145_54_2 i) _)
      colCert_145_54_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T145_54
      hfix145_54 hinj145_54 hcardT145_54
      (fun i => conj_mem_of_fixedPoints _ _ (T145_54 i) (hfix145_54 i) _)
      ⟨145, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T145_54_2 Q2.hfix145_54_2 Q2.hinj145_54_2
      Q2.hcardT145_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_54_2 i) (Q2.hfix145_54_2 i) _)
      colCert_145_54_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T145_54
      hfix145_54 hinj145_54 hcardT145_54
      (fun i => conj_mem_of_fixedPoints _ _ (T145_54 i) (hfix145_54 i) _)
      ⟨145, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T145_54_2 Q2.hfix145_54_2 Q2.hinj145_54_2
      Q2.hcardT145_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_54_2 i) (Q2.hfix145_54_2 i) _)
      colCert_145_54_5.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T145_54
      hfix145_54 hinj145_54 hcardT145_54
      (fun i => conj_mem_of_fixedPoints _ _ (T145_54 i) (hfix145_54 i) _)
      ⟨145, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T145_54_2 Q2.hfix145_54_2 Q2.hinj145_54_2
      Q2.hcardT145_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_54_2 i) (Q2.hfix145_54_2 i) _)
      colCert_145_54_10.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T145_54
      hfix145_54 hinj145_54 hcardT145_54
      (fun i => conj_mem_of_fixedPoints _ _ (T145_54 i) (hfix145_54 i) _)
      ⟨145, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T145_54_2 Q2.hfix145_54_2 Q2.hinj145_54_2
      Q2.hcardT145_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_54_2 i) (Q2.hfix145_54_2 i) _)
      colCert_145_54_15.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T145_54
      hfix145_54 hinj145_54 hcardT145_54
      (fun i => conj_mem_of_fixedPoints _ _ (T145_54 i) (hfix145_54 i) _)
      ⟨145, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T145_54_2 Q2.hfix145_54_2 Q2.hinj145_54_2
      Q2.hcardT145_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_54_2 i) (Q2.hfix145_54_2 i) _)
      colCert_145_54_20.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_0 (hp : 0 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 0 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_0.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_1 (hp : 1 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 1 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 1 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_1.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_2 (hp : 2 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 2 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 2 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_2.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_3 (hp : 3 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 3 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 3 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_3.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_4 (hp : 4 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 4 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 4 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_4.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_5 (hp : 5 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 5 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 5 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_5.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_10 (hp : 10 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 10 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 10 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_10.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_15 (hp : 15 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 15 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 15 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_15.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_20 (hp : 20 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 20 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 20 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_20.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_25 (hp : 25 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 25 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 25 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_25.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_50 (hp : 50 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 50 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 50 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_50.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_75 (hp : 75 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 75 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 75 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_75.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_105_100 (hp : 100 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 100 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp)) T145_105
      hfix145_105 hinj145_105 hcardT145_105
      (fun i => conj_mem_of_fixedPoints _ _ (T145_105 i) (hfix145_105 i) _)
      ⟨145, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 100 hp) Q2.T145_105_2 Q2.hfix145_105_2 Q2.hinj145_105_2
      Q2.hcardT145_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_105_2 i) (Q2.hfix145_105_2 i) _)
      colCert_145_105_100.hD ?_).symm
  rw [alnId_145 j hj]


theorem leaf_145_106_0 (hp : 0 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 0 hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨145, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨145, by decide⟩ (listedAt ⟨145, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp)) T145_106
      hfix145_106 hinj145_106 hcardT145_106
      (fun i => conj_mem_of_fixedPoints _ _ (T145_106 i) (hfix145_106 i) _)
      ⟨145, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨145, by decide⟩ (Q2.listedAt ⟨145, by decide⟩
        (alnCheck_rep ⟨145, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 0 hp) Q2.T145_106_2 Q2.hfix145_106_2 Q2.hinj145_106_2
      Q2.hcardT145_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T145_106_2 i) (Q2.hfix145_106_2 i) _)
      colCert_145_106_0.hD ?_).symm
  rw [alnId_145 j hj]


end LeanDring.P5Presentation
