/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C022
import LeanDring.P5.Data.ColCdd.C023
import LeanDring.P5.Data.ColCdd.C024
import LeanDring.P5.Data.ColRestCheap.C112
import LeanDring.P5.Data.ColRestCheap.C113
import LeanDring.P5.Data.ColRestCheap.C114
import LeanDring.P5.Data.ColRestCheap.C115
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C037
import LeanDring.P5.Data.SpeciesDiv.C038

/-! # Stage-5 leaves, chunk 49 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_147_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T147_25
      hfix147_25 hinj147_25 hcardT147_25
      (fun i => conj_mem_of_fixedPoints _ _ (T147_25 i) (hfix147_25 i) _)
      ⟨147, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T147_25_2 Q2.hfix147_25_2 Q2.hinj147_25_2
      Q2.hcardT147_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_25_2 i) (Q2.hfix147_25_2 i) _)
      colCert_147_25_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T147_25
      hfix147_25 hinj147_25 hcardT147_25
      (fun i => conj_mem_of_fixedPoints _ _ (T147_25 i) (hfix147_25 i) _)
      ⟨147, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T147_25_2 Q2.hfix147_25_2 Q2.hinj147_25_2
      Q2.hcardT147_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_25_2 i) (Q2.hfix147_25_2 i) _)
      colCert_147_25_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T147_25
      hfix147_25 hinj147_25 hcardT147_25
      (fun i => conj_mem_of_fixedPoints _ _ (T147_25 i) (hfix147_25 i) _)
      ⟨147, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T147_25_2 Q2.hfix147_25_2 Q2.hinj147_25_2
      Q2.hcardT147_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_25_2 i) (Q2.hfix147_25_2 i) _)
      colCert_147_25_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T147_26
      hfix147_26 hinj147_26 hcardT147_26
      (fun i => conj_mem_of_fixedPoints _ _ (T147_26 i) (hfix147_26 i) _)
      ⟨147, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T147_26_2 Q2.hfix147_26_2 Q2.hinj147_26_2
      Q2.hcardT147_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_26_2 i) (Q2.hfix147_26_2 i) _)
      colCert_147_26_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T147_26
      hfix147_26 hinj147_26 hcardT147_26
      (fun i => conj_mem_of_fixedPoints _ _ (T147_26 i) (hfix147_26 i) _)
      ⟨147, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T147_26_2 Q2.hfix147_26_2 Q2.hinj147_26_2
      Q2.hcardT147_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_26_2 i) (Q2.hfix147_26_2 i) _)
      colCert_147_26_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T147_26
      hfix147_26 hinj147_26 hcardT147_26
      (fun i => conj_mem_of_fixedPoints _ _ (T147_26 i) (hfix147_26 i) _)
      ⟨147, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T147_26_2 Q2.hfix147_26_2 Q2.hinj147_26_2
      Q2.hcardT147_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_26_2 i) (Q2.hfix147_26_2 i) _)
      colCert_147_26_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T147_26
      hfix147_26 hinj147_26 hcardT147_26
      (fun i => conj_mem_of_fixedPoints _ _ (T147_26 i) (hfix147_26 i) _)
      ⟨147, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T147_26_2 Q2.hfix147_26_2 Q2.hinj147_26_2
      Q2.hcardT147_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_26_2 i) (Q2.hfix147_26_2 i) _)
      colCert_147_26_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T147_26
      hfix147_26 hinj147_26 hcardT147_26
      (fun i => conj_mem_of_fixedPoints _ _ (T147_26 i) (hfix147_26 i) _)
      ⟨147, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T147_26_2 Q2.hfix147_26_2 Q2.hinj147_26_2
      Q2.hcardT147_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_26_2 i) (Q2.hfix147_26_2 i) _)
      colCert_147_26_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T147_26
      hfix147_26 hinj147_26 hcardT147_26
      (fun i => conj_mem_of_fixedPoints _ _ (T147_26 i) (hfix147_26 i) _)
      ⟨147, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T147_26_2 Q2.hfix147_26_2 Q2.hinj147_26_2
      Q2.hcardT147_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_26_2 i) (Q2.hfix147_26_2 i) _)
      colCert_147_26_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T147_26
      hfix147_26 hinj147_26 hcardT147_26
      (fun i => conj_mem_of_fixedPoints _ _ (T147_26 i) (hfix147_26 i) _)
      ⟨147, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T147_26_2 Q2.hfix147_26_2 Q2.hinj147_26_2
      Q2.hcardT147_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_26_2 i) (Q2.hfix147_26_2 i) _)
      colCert_147_26_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T147_26
      hfix147_26 hinj147_26 hcardT147_26
      (fun i => conj_mem_of_fixedPoints _ _ (T147_26 i) (hfix147_26 i) _)
      ⟨147, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T147_26_2 Q2.hfix147_26_2 Q2.hinj147_26_2
      Q2.hcardT147_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_26_2 i) (Q2.hfix147_26_2 i) _)
      colCert_147_26_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T147_26
      hfix147_26 hinj147_26 hcardT147_26
      (fun i => conj_mem_of_fixedPoints _ _ (T147_26 i) (hfix147_26 i) _)
      ⟨147, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T147_26_2 Q2.hfix147_26_2 Q2.hinj147_26_2
      Q2.hcardT147_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_26_2 i) (Q2.hfix147_26_2 i) _)
      colCert_147_26_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T147_27
      hfix147_27 hinj147_27 hcardT147_27
      (fun i => conj_mem_of_fixedPoints _ _ (T147_27 i) (hfix147_27 i) _)
      ⟨147, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T147_27_2 Q2.hfix147_27_2 Q2.hinj147_27_2
      Q2.hcardT147_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_27_2 i) (Q2.hfix147_27_2 i) _)
      colCert_147_27_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T147_27
      hfix147_27 hinj147_27 hcardT147_27
      (fun i => conj_mem_of_fixedPoints _ _ (T147_27 i) (hfix147_27 i) _)
      ⟨147, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T147_27_2 Q2.hfix147_27_2 Q2.hinj147_27_2
      Q2.hcardT147_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_27_2 i) (Q2.hfix147_27_2 i) _)
      colCert_147_27_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T147_27
      hfix147_27 hinj147_27 hcardT147_27
      (fun i => conj_mem_of_fixedPoints _ _ (T147_27 i) (hfix147_27 i) _)
      ⟨147, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T147_27_2 Q2.hfix147_27_2 Q2.hinj147_27_2
      Q2.hcardT147_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_27_2 i) (Q2.hfix147_27_2 i) _)
      colCert_147_27_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T147_27
      hfix147_27 hinj147_27 hcardT147_27
      (fun i => conj_mem_of_fixedPoints _ _ (T147_27 i) (hfix147_27 i) _)
      ⟨147, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T147_27_2 Q2.hfix147_27_2 Q2.hinj147_27_2
      Q2.hcardT147_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_27_2 i) (Q2.hfix147_27_2 i) _)
      colCert_147_27_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T147_27
      hfix147_27 hinj147_27 hcardT147_27
      (fun i => conj_mem_of_fixedPoints _ _ (T147_27 i) (hfix147_27 i) _)
      ⟨147, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T147_27_2 Q2.hfix147_27_2 Q2.hinj147_27_2
      Q2.hcardT147_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_27_2 i) (Q2.hfix147_27_2 i) _)
      colCert_147_27_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T147_27
      hfix147_27 hinj147_27 hcardT147_27
      (fun i => conj_mem_of_fixedPoints _ _ (T147_27 i) (hfix147_27 i) _)
      ⟨147, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T147_27_2 Q2.hfix147_27_2 Q2.hinj147_27_2
      Q2.hcardT147_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_27_2 i) (Q2.hfix147_27_2 i) _)
      colCert_147_27_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T147_27
      hfix147_27 hinj147_27 hcardT147_27
      (fun i => conj_mem_of_fixedPoints _ _ (T147_27 i) (hfix147_27 i) _)
      ⟨147, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T147_27_2 Q2.hfix147_27_2 Q2.hinj147_27_2
      Q2.hcardT147_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_27_2 i) (Q2.hfix147_27_2 i) _)
      colCert_147_27_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T147_27
      hfix147_27 hinj147_27 hcardT147_27
      (fun i => conj_mem_of_fixedPoints _ _ (T147_27 i) (hfix147_27 i) _)
      ⟨147, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T147_27_2 Q2.hfix147_27_2 Q2.hinj147_27_2
      Q2.hcardT147_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_27_2 i) (Q2.hfix147_27_2 i) _)
      colCert_147_27_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T147_27
      hfix147_27 hinj147_27 hcardT147_27
      (fun i => conj_mem_of_fixedPoints _ _ (T147_27 i) (hfix147_27 i) _)
      ⟨147, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T147_27_2 Q2.hfix147_27_2 Q2.hinj147_27_2
      Q2.hcardT147_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_27_2 i) (Q2.hfix147_27_2 i) _)
      colCert_147_27_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T147_28
      hfix147_28 hinj147_28 hcardT147_28
      (fun i => conj_mem_of_fixedPoints _ _ (T147_28 i) (hfix147_28 i) _)
      ⟨147, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T147_28_2 Q2.hfix147_28_2 Q2.hinj147_28_2
      Q2.hcardT147_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_28_2 i) (Q2.hfix147_28_2 i) _)
      colCert_147_28_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T147_28
      hfix147_28 hinj147_28 hcardT147_28
      (fun i => conj_mem_of_fixedPoints _ _ (T147_28 i) (hfix147_28 i) _)
      ⟨147, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T147_28_2 Q2.hfix147_28_2 Q2.hinj147_28_2
      Q2.hcardT147_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_28_2 i) (Q2.hfix147_28_2 i) _)
      colCert_147_28_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T147_28
      hfix147_28 hinj147_28 hcardT147_28
      (fun i => conj_mem_of_fixedPoints _ _ (T147_28 i) (hfix147_28 i) _)
      ⟨147, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T147_28_2 Q2.hfix147_28_2 Q2.hinj147_28_2
      Q2.hcardT147_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_28_2 i) (Q2.hfix147_28_2 i) _)
      colCert_147_28_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T147_28
      hfix147_28 hinj147_28 hcardT147_28
      (fun i => conj_mem_of_fixedPoints _ _ (T147_28 i) (hfix147_28 i) _)
      ⟨147, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T147_28_2 Q2.hfix147_28_2 Q2.hinj147_28_2
      Q2.hcardT147_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_28_2 i) (Q2.hfix147_28_2 i) _)
      colCert_147_28_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T147_28
      hfix147_28 hinj147_28 hcardT147_28
      (fun i => conj_mem_of_fixedPoints _ _ (T147_28 i) (hfix147_28 i) _)
      ⟨147, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T147_28_2 Q2.hfix147_28_2 Q2.hinj147_28_2
      Q2.hcardT147_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_28_2 i) (Q2.hfix147_28_2 i) _)
      colCert_147_28_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T147_28
      hfix147_28 hinj147_28 hcardT147_28
      (fun i => conj_mem_of_fixedPoints _ _ (T147_28 i) (hfix147_28 i) _)
      ⟨147, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T147_28_2 Q2.hfix147_28_2 Q2.hinj147_28_2
      Q2.hcardT147_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_28_2 i) (Q2.hfix147_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T147_28 = colFn colCertDiv_147_28_5.D1 (m := 1) from colCertDiv_147_28_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 5 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T147_28_2 = colFn colCertDiv_147_28_5.D2 (m := 1) from colCertDiv_147_28_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_28_5_match


theorem leaf_147_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T147_28
      hfix147_28 hinj147_28 hcardT147_28
      (fun i => conj_mem_of_fixedPoints _ _ (T147_28 i) (hfix147_28 i) _)
      ⟨147, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T147_28_2 Q2.hfix147_28_2 Q2.hinj147_28_2
      Q2.hcardT147_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_28_2 i) (Q2.hfix147_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T147_28 = colFn colCertDiv_147_28_10.D1 (m := 1) from colCertDiv_147_28_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 10 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T147_28_2 = colFn colCertDiv_147_28_10.D2 (m := 1) from colCertDiv_147_28_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_28_10_match


theorem leaf_147_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T147_28
      hfix147_28 hinj147_28 hcardT147_28
      (fun i => conj_mem_of_fixedPoints _ _ (T147_28 i) (hfix147_28 i) _)
      ⟨147, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T147_28_2 Q2.hfix147_28_2 Q2.hinj147_28_2
      Q2.hcardT147_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_28_2 i) (Q2.hfix147_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T147_28 = colFn colCertDiv_147_28_15.D1 (m := 1) from colCertDiv_147_28_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 15 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T147_28_2 = colFn colCertDiv_147_28_15.D2 (m := 1) from colCertDiv_147_28_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_28_15_match


theorem leaf_147_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T147_28
      hfix147_28 hinj147_28 hcardT147_28
      (fun i => conj_mem_of_fixedPoints _ _ (T147_28 i) (hfix147_28 i) _)
      ⟨147, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T147_28_2 Q2.hfix147_28_2 Q2.hinj147_28_2
      Q2.hcardT147_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_28_2 i) (Q2.hfix147_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T147_28 = colFn colCertDiv_147_28_20.D1 (m := 1) from colCertDiv_147_28_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 20 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T147_28_2 = colFn colCertDiv_147_28_20.D2 (m := 1) from colCertDiv_147_28_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_28_20_match


theorem leaf_147_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T147_29
      hfix147_29 hinj147_29 hcardT147_29
      (fun i => conj_mem_of_fixedPoints _ _ (T147_29 i) (hfix147_29 i) _)
      ⟨147, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T147_29_2 Q2.hfix147_29_2 Q2.hinj147_29_2
      Q2.hcardT147_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_29_2 i) (Q2.hfix147_29_2 i) _)
      colCert_147_29_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T147_29
      hfix147_29 hinj147_29 hcardT147_29
      (fun i => conj_mem_of_fixedPoints _ _ (T147_29 i) (hfix147_29 i) _)
      ⟨147, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T147_29_2 Q2.hfix147_29_2 Q2.hinj147_29_2
      Q2.hcardT147_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_29_2 i) (Q2.hfix147_29_2 i) _)
      colCert_147_29_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T147_29
      hfix147_29 hinj147_29 hcardT147_29
      (fun i => conj_mem_of_fixedPoints _ _ (T147_29 i) (hfix147_29 i) _)
      ⟨147, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T147_29_2 Q2.hfix147_29_2 Q2.hinj147_29_2
      Q2.hcardT147_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_29_2 i) (Q2.hfix147_29_2 i) _)
      colCert_147_29_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T147_29
      hfix147_29 hinj147_29 hcardT147_29
      (fun i => conj_mem_of_fixedPoints _ _ (T147_29 i) (hfix147_29 i) _)
      ⟨147, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T147_29_2 Q2.hfix147_29_2 Q2.hinj147_29_2
      Q2.hcardT147_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_29_2 i) (Q2.hfix147_29_2 i) _)
      colCert_147_29_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T147_29
      hfix147_29 hinj147_29 hcardT147_29
      (fun i => conj_mem_of_fixedPoints _ _ (T147_29 i) (hfix147_29 i) _)
      ⟨147, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T147_29_2 Q2.hfix147_29_2 Q2.hinj147_29_2
      Q2.hcardT147_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_29_2 i) (Q2.hfix147_29_2 i) _)
      colCert_147_29_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T147_29
      hfix147_29 hinj147_29 hcardT147_29
      (fun i => conj_mem_of_fixedPoints _ _ (T147_29 i) (hfix147_29 i) _)
      ⟨147, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T147_29_2 Q2.hfix147_29_2 Q2.hinj147_29_2
      Q2.hcardT147_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_29_2 i) (Q2.hfix147_29_2 i) _)
      colCert_147_29_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T147_29
      hfix147_29 hinj147_29 hcardT147_29
      (fun i => conj_mem_of_fixedPoints _ _ (T147_29 i) (hfix147_29 i) _)
      ⟨147, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T147_29_2 Q2.hfix147_29_2 Q2.hinj147_29_2
      Q2.hcardT147_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_29_2 i) (Q2.hfix147_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T147_29 = colFn colCertDiv_147_29_10.D1 (m := 1) from colCertDiv_147_29_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 10 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T147_29_2 = colFn colCertDiv_147_29_10.D2 (m := 1) from colCertDiv_147_29_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_29_10_match


theorem leaf_147_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T147_29
      hfix147_29 hinj147_29 hcardT147_29
      (fun i => conj_mem_of_fixedPoints _ _ (T147_29 i) (hfix147_29 i) _)
      ⟨147, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T147_29_2 Q2.hfix147_29_2 Q2.hinj147_29_2
      Q2.hcardT147_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_29_2 i) (Q2.hfix147_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T147_29 = colFn colCertDiv_147_29_15.D1 (m := 1) from colCertDiv_147_29_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 15 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T147_29_2 = colFn colCertDiv_147_29_15.D2 (m := 1) from colCertDiv_147_29_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_29_15_match


theorem leaf_147_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T147_29
      hfix147_29 hinj147_29 hcardT147_29
      (fun i => conj_mem_of_fixedPoints _ _ (T147_29 i) (hfix147_29 i) _)
      ⟨147, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T147_29_2 Q2.hfix147_29_2 Q2.hinj147_29_2
      Q2.hcardT147_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_29_2 i) (Q2.hfix147_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T147_29 = colFn colCertDiv_147_29_20.D1 (m := 1) from colCertDiv_147_29_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 20 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T147_29_2 = colFn colCertDiv_147_29_20.D2 (m := 1) from colCertDiv_147_29_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_29_20_match


theorem leaf_147_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T147_30
      hfix147_30 hinj147_30 hcardT147_30
      (fun i => conj_mem_of_fixedPoints _ _ (T147_30 i) (hfix147_30 i) _)
      ⟨147, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T147_30_2 Q2.hfix147_30_2 Q2.hinj147_30_2
      Q2.hcardT147_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_30_2 i) (Q2.hfix147_30_2 i) _)
      colCert_147_30_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T147_30
      hfix147_30 hinj147_30 hcardT147_30
      (fun i => conj_mem_of_fixedPoints _ _ (T147_30 i) (hfix147_30 i) _)
      ⟨147, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T147_30_2 Q2.hfix147_30_2 Q2.hinj147_30_2
      Q2.hcardT147_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_30_2 i) (Q2.hfix147_30_2 i) _)
      colCert_147_30_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T147_30
      hfix147_30 hinj147_30 hcardT147_30
      (fun i => conj_mem_of_fixedPoints _ _ (T147_30 i) (hfix147_30 i) _)
      ⟨147, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T147_30_2 Q2.hfix147_30_2 Q2.hinj147_30_2
      Q2.hcardT147_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_30_2 i) (Q2.hfix147_30_2 i) _)
      colCert_147_30_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T147_30
      hfix147_30 hinj147_30 hcardT147_30
      (fun i => conj_mem_of_fixedPoints _ _ (T147_30 i) (hfix147_30 i) _)
      ⟨147, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T147_30_2 Q2.hfix147_30_2 Q2.hinj147_30_2
      Q2.hcardT147_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_30_2 i) (Q2.hfix147_30_2 i) _)
      colCert_147_30_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T147_30
      hfix147_30 hinj147_30 hcardT147_30
      (fun i => conj_mem_of_fixedPoints _ _ (T147_30 i) (hfix147_30 i) _)
      ⟨147, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T147_30_2 Q2.hfix147_30_2 Q2.hinj147_30_2
      Q2.hcardT147_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_30_2 i) (Q2.hfix147_30_2 i) _)
      colCert_147_30_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T147_30
      hfix147_30 hinj147_30 hcardT147_30
      (fun i => conj_mem_of_fixedPoints _ _ (T147_30 i) (hfix147_30 i) _)
      ⟨147, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T147_30_2 Q2.hfix147_30_2 Q2.hinj147_30_2
      Q2.hcardT147_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_30_2 i) (Q2.hfix147_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T147_30 = colFn colCertDiv_147_30_5.D1 (m := 1) from colCertDiv_147_30_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 5 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T147_30_2 = colFn colCertDiv_147_30_5.D2 (m := 1) from colCertDiv_147_30_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_30_5_match


theorem leaf_147_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T147_30
      hfix147_30 hinj147_30 hcardT147_30
      (fun i => conj_mem_of_fixedPoints _ _ (T147_30 i) (hfix147_30 i) _)
      ⟨147, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T147_30_2 Q2.hfix147_30_2 Q2.hinj147_30_2
      Q2.hcardT147_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_30_2 i) (Q2.hfix147_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T147_30 = colFn colCertDiv_147_30_10.D1 (m := 1) from colCertDiv_147_30_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 10 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T147_30_2 = colFn colCertDiv_147_30_10.D2 (m := 1) from colCertDiv_147_30_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_30_10_match


theorem leaf_147_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T147_30
      hfix147_30 hinj147_30 hcardT147_30
      (fun i => conj_mem_of_fixedPoints _ _ (T147_30 i) (hfix147_30 i) _)
      ⟨147, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T147_30_2 Q2.hfix147_30_2 Q2.hinj147_30_2
      Q2.hcardT147_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_30_2 i) (Q2.hfix147_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T147_30 = colFn colCertDiv_147_30_15.D1 (m := 1) from colCertDiv_147_30_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 15 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T147_30_2 = colFn colCertDiv_147_30_15.D2 (m := 1) from colCertDiv_147_30_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_30_15_match


theorem leaf_147_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T147_30
      hfix147_30 hinj147_30 hcardT147_30
      (fun i => conj_mem_of_fixedPoints _ _ (T147_30 i) (hfix147_30 i) _)
      ⟨147, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T147_30_2 Q2.hfix147_30_2 Q2.hinj147_30_2
      Q2.hcardT147_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_30_2 i) (Q2.hfix147_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T147_30 = colFn colCertDiv_147_30_20.D1 (m := 1) from colCertDiv_147_30_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 20 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T147_30_2 = colFn colCertDiv_147_30_20.D2 (m := 1) from colCertDiv_147_30_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_30_20_match


theorem leaf_147_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T147_31
      hfix147_31 hinj147_31 hcardT147_31
      (fun i => conj_mem_of_fixedPoints _ _ (T147_31 i) (hfix147_31 i) _)
      ⟨147, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T147_31_2 Q2.hfix147_31_2 Q2.hinj147_31_2
      Q2.hcardT147_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_31_2 i) (Q2.hfix147_31_2 i) _)
      colCert_147_31_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T147_31
      hfix147_31 hinj147_31 hcardT147_31
      (fun i => conj_mem_of_fixedPoints _ _ (T147_31 i) (hfix147_31 i) _)
      ⟨147, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T147_31_2 Q2.hfix147_31_2 Q2.hinj147_31_2
      Q2.hcardT147_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_31_2 i) (Q2.hfix147_31_2 i) _)
      colCert_147_31_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T147_31
      hfix147_31 hinj147_31 hcardT147_31
      (fun i => conj_mem_of_fixedPoints _ _ (T147_31 i) (hfix147_31 i) _)
      ⟨147, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T147_31_2 Q2.hfix147_31_2 Q2.hinj147_31_2
      Q2.hcardT147_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_31_2 i) (Q2.hfix147_31_2 i) _)
      colCert_147_31_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T147_31
      hfix147_31 hinj147_31 hcardT147_31
      (fun i => conj_mem_of_fixedPoints _ _ (T147_31 i) (hfix147_31 i) _)
      ⟨147, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T147_31_2 Q2.hfix147_31_2 Q2.hinj147_31_2
      Q2.hcardT147_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_31_2 i) (Q2.hfix147_31_2 i) _)
      colCert_147_31_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T147_31
      hfix147_31 hinj147_31 hcardT147_31
      (fun i => conj_mem_of_fixedPoints _ _ (T147_31 i) (hfix147_31 i) _)
      ⟨147, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T147_31_2 Q2.hfix147_31_2 Q2.hinj147_31_2
      Q2.hcardT147_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_31_2 i) (Q2.hfix147_31_2 i) _)
      colCert_147_31_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T147_31
      hfix147_31 hinj147_31 hcardT147_31
      (fun i => conj_mem_of_fixedPoints _ _ (T147_31 i) (hfix147_31 i) _)
      ⟨147, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T147_31_2 Q2.hfix147_31_2 Q2.hinj147_31_2
      Q2.hcardT147_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_31_2 i) (Q2.hfix147_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T147_31 = colFn colCertDiv_147_31_5.D1 (m := 1) from colCertDiv_147_31_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 5 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T147_31_2 = colFn colCertDiv_147_31_5.D2 (m := 1) from colCertDiv_147_31_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_31_5_match


theorem leaf_147_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T147_31
      hfix147_31 hinj147_31 hcardT147_31
      (fun i => conj_mem_of_fixedPoints _ _ (T147_31 i) (hfix147_31 i) _)
      ⟨147, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T147_31_2 Q2.hfix147_31_2 Q2.hinj147_31_2
      Q2.hcardT147_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_31_2 i) (Q2.hfix147_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T147_31 = colFn colCertDiv_147_31_10.D1 (m := 1) from colCertDiv_147_31_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 10 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T147_31_2 = colFn colCertDiv_147_31_10.D2 (m := 1) from colCertDiv_147_31_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_31_10_match


theorem leaf_147_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T147_31
      hfix147_31 hinj147_31 hcardT147_31
      (fun i => conj_mem_of_fixedPoints _ _ (T147_31 i) (hfix147_31 i) _)
      ⟨147, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T147_31_2 Q2.hfix147_31_2 Q2.hinj147_31_2
      Q2.hcardT147_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_31_2 i) (Q2.hfix147_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T147_31 = colFn colCertDiv_147_31_15.D1 (m := 1) from colCertDiv_147_31_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 15 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T147_31_2 = colFn colCertDiv_147_31_15.D2 (m := 1) from colCertDiv_147_31_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_31_15_match


theorem leaf_147_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T147_31
      hfix147_31 hinj147_31 hcardT147_31
      (fun i => conj_mem_of_fixedPoints _ _ (T147_31 i) (hfix147_31 i) _)
      ⟨147, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T147_31_2 Q2.hfix147_31_2 Q2.hinj147_31_2
      Q2.hcardT147_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_31_2 i) (Q2.hfix147_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T147_31 = colFn colCertDiv_147_31_20.D1 (m := 1) from colCertDiv_147_31_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 20 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T147_31_2 = colFn colCertDiv_147_31_20.D2 (m := 1) from colCertDiv_147_31_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_31_20_match


theorem leaf_147_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T147_32
      hfix147_32 hinj147_32 hcardT147_32
      (fun i => conj_mem_of_fixedPoints _ _ (T147_32 i) (hfix147_32 i) _)
      ⟨147, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T147_32_2 Q2.hfix147_32_2 Q2.hinj147_32_2
      Q2.hcardT147_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_32_2 i) (Q2.hfix147_32_2 i) _)
      colCert_147_32_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T147_32
      hfix147_32 hinj147_32 hcardT147_32
      (fun i => conj_mem_of_fixedPoints _ _ (T147_32 i) (hfix147_32 i) _)
      ⟨147, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T147_32_2 Q2.hfix147_32_2 Q2.hinj147_32_2
      Q2.hcardT147_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_32_2 i) (Q2.hfix147_32_2 i) _)
      colCert_147_32_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T147_32
      hfix147_32 hinj147_32 hcardT147_32
      (fun i => conj_mem_of_fixedPoints _ _ (T147_32 i) (hfix147_32 i) _)
      ⟨147, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T147_32_2 Q2.hfix147_32_2 Q2.hinj147_32_2
      Q2.hcardT147_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_32_2 i) (Q2.hfix147_32_2 i) _)
      colCert_147_32_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T147_32
      hfix147_32 hinj147_32 hcardT147_32
      (fun i => conj_mem_of_fixedPoints _ _ (T147_32 i) (hfix147_32 i) _)
      ⟨147, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T147_32_2 Q2.hfix147_32_2 Q2.hinj147_32_2
      Q2.hcardT147_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_32_2 i) (Q2.hfix147_32_2 i) _)
      colCert_147_32_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T147_32
      hfix147_32 hinj147_32 hcardT147_32
      (fun i => conj_mem_of_fixedPoints _ _ (T147_32 i) (hfix147_32 i) _)
      ⟨147, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T147_32_2 Q2.hfix147_32_2 Q2.hinj147_32_2
      Q2.hcardT147_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_32_2 i) (Q2.hfix147_32_2 i) _)
      colCert_147_32_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T147_32
      hfix147_32 hinj147_32 hcardT147_32
      (fun i => conj_mem_of_fixedPoints _ _ (T147_32 i) (hfix147_32 i) _)
      ⟨147, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T147_32_2 Q2.hfix147_32_2 Q2.hinj147_32_2
      Q2.hcardT147_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_32_2 i) (Q2.hfix147_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T147_32 = colFn colCertDiv_147_32_5.D1 (m := 1) from colCertDiv_147_32_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 5 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T147_32_2 = colFn colCertDiv_147_32_5.D2 (m := 1) from colCertDiv_147_32_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_32_5_match


theorem leaf_147_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T147_32
      hfix147_32 hinj147_32 hcardT147_32
      (fun i => conj_mem_of_fixedPoints _ _ (T147_32 i) (hfix147_32 i) _)
      ⟨147, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T147_32_2 Q2.hfix147_32_2 Q2.hinj147_32_2
      Q2.hcardT147_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_32_2 i) (Q2.hfix147_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T147_32 = colFn colCertDiv_147_32_10.D1 (m := 1) from colCertDiv_147_32_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 10 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T147_32_2 = colFn colCertDiv_147_32_10.D2 (m := 1) from colCertDiv_147_32_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_32_10_match


theorem leaf_147_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T147_32
      hfix147_32 hinj147_32 hcardT147_32
      (fun i => conj_mem_of_fixedPoints _ _ (T147_32 i) (hfix147_32 i) _)
      ⟨147, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T147_32_2 Q2.hfix147_32_2 Q2.hinj147_32_2
      Q2.hcardT147_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_32_2 i) (Q2.hfix147_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T147_32 = colFn colCertDiv_147_32_15.D1 (m := 1) from colCertDiv_147_32_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 15 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T147_32_2 = colFn colCertDiv_147_32_15.D2 (m := 1) from colCertDiv_147_32_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_32_15_match


theorem leaf_147_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T147_32
      hfix147_32 hinj147_32 hcardT147_32
      (fun i => conj_mem_of_fixedPoints _ _ (T147_32 i) (hfix147_32 i) _)
      ⟨147, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T147_32_2 Q2.hfix147_32_2 Q2.hinj147_32_2
      Q2.hcardT147_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_32_2 i) (Q2.hfix147_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T147_32 = colFn colCertDiv_147_32_20.D1 (m := 1) from colCertDiv_147_32_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 20 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T147_32_2 = colFn colCertDiv_147_32_20.D2 (m := 1) from colCertDiv_147_32_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_32_20_match


theorem leaf_147_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T147_33
      hfix147_33 hinj147_33 hcardT147_33
      (fun i => conj_mem_of_fixedPoints _ _ (T147_33 i) (hfix147_33 i) _)
      ⟨147, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T147_33_2 Q2.hfix147_33_2 Q2.hinj147_33_2
      Q2.hcardT147_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_33_2 i) (Q2.hfix147_33_2 i) _)
      colCert_147_33_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T147_33
      hfix147_33 hinj147_33 hcardT147_33
      (fun i => conj_mem_of_fixedPoints _ _ (T147_33 i) (hfix147_33 i) _)
      ⟨147, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T147_33_2 Q2.hfix147_33_2 Q2.hinj147_33_2
      Q2.hcardT147_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_33_2 i) (Q2.hfix147_33_2 i) _)
      colCert_147_33_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T147_33
      hfix147_33 hinj147_33 hcardT147_33
      (fun i => conj_mem_of_fixedPoints _ _ (T147_33 i) (hfix147_33 i) _)
      ⟨147, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T147_33_2 Q2.hfix147_33_2 Q2.hinj147_33_2
      Q2.hcardT147_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_33_2 i) (Q2.hfix147_33_2 i) _)
      colCert_147_33_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T147_33
      hfix147_33 hinj147_33 hcardT147_33
      (fun i => conj_mem_of_fixedPoints _ _ (T147_33 i) (hfix147_33 i) _)
      ⟨147, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T147_33_2 Q2.hfix147_33_2 Q2.hinj147_33_2
      Q2.hcardT147_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_33_2 i) (Q2.hfix147_33_2 i) _)
      colCert_147_33_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T147_33
      hfix147_33 hinj147_33 hcardT147_33
      (fun i => conj_mem_of_fixedPoints _ _ (T147_33 i) (hfix147_33 i) _)
      ⟨147, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T147_33_2 Q2.hfix147_33_2 Q2.hinj147_33_2
      Q2.hcardT147_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_33_2 i) (Q2.hfix147_33_2 i) _)
      colCert_147_33_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T147_33
      hfix147_33 hinj147_33 hcardT147_33
      (fun i => conj_mem_of_fixedPoints _ _ (T147_33 i) (hfix147_33 i) _)
      ⟨147, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T147_33_2 Q2.hfix147_33_2 Q2.hinj147_33_2
      Q2.hcardT147_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_33_2 i) (Q2.hfix147_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T147_33 = colFn colCertDiv_147_33_5.D1 (m := 1) from colCertDiv_147_33_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T147_33_2 = colFn colCertDiv_147_33_5.D2 (m := 1) from colCertDiv_147_33_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_33_5_match


theorem leaf_147_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T147_33
      hfix147_33 hinj147_33 hcardT147_33
      (fun i => conj_mem_of_fixedPoints _ _ (T147_33 i) (hfix147_33 i) _)
      ⟨147, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T147_33_2 Q2.hfix147_33_2 Q2.hinj147_33_2
      Q2.hcardT147_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_33_2 i) (Q2.hfix147_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T147_33 = colFn colCertDiv_147_33_10.D1 (m := 1) from colCertDiv_147_33_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T147_33_2 = colFn colCertDiv_147_33_10.D2 (m := 1) from colCertDiv_147_33_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_33_10_match


theorem leaf_147_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T147_33
      hfix147_33 hinj147_33 hcardT147_33
      (fun i => conj_mem_of_fixedPoints _ _ (T147_33 i) (hfix147_33 i) _)
      ⟨147, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T147_33_2 Q2.hfix147_33_2 Q2.hinj147_33_2
      Q2.hcardT147_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_33_2 i) (Q2.hfix147_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T147_33 = colFn colCertDiv_147_33_15.D1 (m := 1) from colCertDiv_147_33_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T147_33_2 = colFn colCertDiv_147_33_15.D2 (m := 1) from colCertDiv_147_33_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_33_15_match


theorem leaf_147_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T147_33
      hfix147_33 hinj147_33 hcardT147_33
      (fun i => conj_mem_of_fixedPoints _ _ (T147_33 i) (hfix147_33 i) _)
      ⟨147, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T147_33_2 Q2.hfix147_33_2 Q2.hinj147_33_2
      Q2.hcardT147_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_33_2 i) (Q2.hfix147_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T147_33 = colFn colCertDiv_147_33_20.D1 (m := 1) from colCertDiv_147_33_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T147_33_2 = colFn colCertDiv_147_33_20.D2 (m := 1) from colCertDiv_147_33_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_33_20_match


theorem leaf_147_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T147_34
      hfix147_34 hinj147_34 hcardT147_34
      (fun i => conj_mem_of_fixedPoints _ _ (T147_34 i) (hfix147_34 i) _)
      ⟨147, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T147_34_2 Q2.hfix147_34_2 Q2.hinj147_34_2
      Q2.hcardT147_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_34_2 i) (Q2.hfix147_34_2 i) _)
      colCert_147_34_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T147_34
      hfix147_34 hinj147_34 hcardT147_34
      (fun i => conj_mem_of_fixedPoints _ _ (T147_34 i) (hfix147_34 i) _)
      ⟨147, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T147_34_2 Q2.hfix147_34_2 Q2.hinj147_34_2
      Q2.hcardT147_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_34_2 i) (Q2.hfix147_34_2 i) _)
      colCert_147_34_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T147_34
      hfix147_34 hinj147_34 hcardT147_34
      (fun i => conj_mem_of_fixedPoints _ _ (T147_34 i) (hfix147_34 i) _)
      ⟨147, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T147_34_2 Q2.hfix147_34_2 Q2.hinj147_34_2
      Q2.hcardT147_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_34_2 i) (Q2.hfix147_34_2 i) _)
      colCert_147_34_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T147_34
      hfix147_34 hinj147_34 hcardT147_34
      (fun i => conj_mem_of_fixedPoints _ _ (T147_34 i) (hfix147_34 i) _)
      ⟨147, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T147_34_2 Q2.hfix147_34_2 Q2.hinj147_34_2
      Q2.hcardT147_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_34_2 i) (Q2.hfix147_34_2 i) _)
      colCert_147_34_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T147_34
      hfix147_34 hinj147_34 hcardT147_34
      (fun i => conj_mem_of_fixedPoints _ _ (T147_34 i) (hfix147_34 i) _)
      ⟨147, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T147_34_2 Q2.hfix147_34_2 Q2.hinj147_34_2
      Q2.hcardT147_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_34_2 i) (Q2.hfix147_34_2 i) _)
      colCert_147_34_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T147_34
      hfix147_34 hinj147_34 hcardT147_34
      (fun i => conj_mem_of_fixedPoints _ _ (T147_34 i) (hfix147_34 i) _)
      ⟨147, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T147_34_2 Q2.hfix147_34_2 Q2.hinj147_34_2
      Q2.hcardT147_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_34_2 i) (Q2.hfix147_34_2 i) _)
      colCert_147_34_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T147_34
      hfix147_34 hinj147_34 hcardT147_34
      (fun i => conj_mem_of_fixedPoints _ _ (T147_34 i) (hfix147_34 i) _)
      ⟨147, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T147_34_2 Q2.hfix147_34_2 Q2.hinj147_34_2
      Q2.hcardT147_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_34_2 i) (Q2.hfix147_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T147_34 = colFn colCertDiv_147_34_10.D1 (m := 1) from colCertDiv_147_34_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 10 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T147_34_2 = colFn colCertDiv_147_34_10.D2 (m := 1) from colCertDiv_147_34_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_34_10_match


theorem leaf_147_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T147_34
      hfix147_34 hinj147_34 hcardT147_34
      (fun i => conj_mem_of_fixedPoints _ _ (T147_34 i) (hfix147_34 i) _)
      ⟨147, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T147_34_2 Q2.hfix147_34_2 Q2.hinj147_34_2
      Q2.hcardT147_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_34_2 i) (Q2.hfix147_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T147_34 = colFn colCertDiv_147_34_15.D1 (m := 1) from colCertDiv_147_34_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 15 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T147_34_2 = colFn colCertDiv_147_34_15.D2 (m := 1) from colCertDiv_147_34_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_34_15_match


theorem leaf_147_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T147_34
      hfix147_34 hinj147_34 hcardT147_34
      (fun i => conj_mem_of_fixedPoints _ _ (T147_34 i) (hfix147_34 i) _)
      ⟨147, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T147_34_2 Q2.hfix147_34_2 Q2.hinj147_34_2
      Q2.hcardT147_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_34_2 i) (Q2.hfix147_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T147_34 = colFn colCertDiv_147_34_20.D1 (m := 1) from colCertDiv_147_34_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 20 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T147_34_2 = colFn colCertDiv_147_34_20.D2 (m := 1) from colCertDiv_147_34_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_34_20_match


theorem leaf_147_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T147_35
      hfix147_35 hinj147_35 hcardT147_35
      (fun i => conj_mem_of_fixedPoints _ _ (T147_35 i) (hfix147_35 i) _)
      ⟨147, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T147_35_2 Q2.hfix147_35_2 Q2.hinj147_35_2
      Q2.hcardT147_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_35_2 i) (Q2.hfix147_35_2 i) _)
      colCert_147_35_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T147_35
      hfix147_35 hinj147_35 hcardT147_35
      (fun i => conj_mem_of_fixedPoints _ _ (T147_35 i) (hfix147_35 i) _)
      ⟨147, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T147_35_2 Q2.hfix147_35_2 Q2.hinj147_35_2
      Q2.hcardT147_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_35_2 i) (Q2.hfix147_35_2 i) _)
      colCert_147_35_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T147_35
      hfix147_35 hinj147_35 hcardT147_35
      (fun i => conj_mem_of_fixedPoints _ _ (T147_35 i) (hfix147_35 i) _)
      ⟨147, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T147_35_2 Q2.hfix147_35_2 Q2.hinj147_35_2
      Q2.hcardT147_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_35_2 i) (Q2.hfix147_35_2 i) _)
      colCert_147_35_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T147_35
      hfix147_35 hinj147_35 hcardT147_35
      (fun i => conj_mem_of_fixedPoints _ _ (T147_35 i) (hfix147_35 i) _)
      ⟨147, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T147_35_2 Q2.hfix147_35_2 Q2.hinj147_35_2
      Q2.hcardT147_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_35_2 i) (Q2.hfix147_35_2 i) _)
      colCert_147_35_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T147_35
      hfix147_35 hinj147_35 hcardT147_35
      (fun i => conj_mem_of_fixedPoints _ _ (T147_35 i) (hfix147_35 i) _)
      ⟨147, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T147_35_2 Q2.hfix147_35_2 Q2.hinj147_35_2
      Q2.hcardT147_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_35_2 i) (Q2.hfix147_35_2 i) _)
      colCert_147_35_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T147_35
      hfix147_35 hinj147_35 hcardT147_35
      (fun i => conj_mem_of_fixedPoints _ _ (T147_35 i) (hfix147_35 i) _)
      ⟨147, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T147_35_2 Q2.hfix147_35_2 Q2.hinj147_35_2
      Q2.hcardT147_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_35_2 i) (Q2.hfix147_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T147_35 = colFn colCertDiv_147_35_5.D1 (m := 1) from colCertDiv_147_35_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 5 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T147_35_2 = colFn colCertDiv_147_35_5.D2 (m := 1) from colCertDiv_147_35_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_35_5_match


theorem leaf_147_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T147_35
      hfix147_35 hinj147_35 hcardT147_35
      (fun i => conj_mem_of_fixedPoints _ _ (T147_35 i) (hfix147_35 i) _)
      ⟨147, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T147_35_2 Q2.hfix147_35_2 Q2.hinj147_35_2
      Q2.hcardT147_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_35_2 i) (Q2.hfix147_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T147_35 = colFn colCertDiv_147_35_10.D1 (m := 1) from colCertDiv_147_35_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 10 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T147_35_2 = colFn colCertDiv_147_35_10.D2 (m := 1) from colCertDiv_147_35_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_35_10_match


theorem leaf_147_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T147_35
      hfix147_35 hinj147_35 hcardT147_35
      (fun i => conj_mem_of_fixedPoints _ _ (T147_35 i) (hfix147_35 i) _)
      ⟨147, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T147_35_2 Q2.hfix147_35_2 Q2.hinj147_35_2
      Q2.hcardT147_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_35_2 i) (Q2.hfix147_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T147_35 = colFn colCertDiv_147_35_15.D1 (m := 1) from colCertDiv_147_35_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 15 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T147_35_2 = colFn colCertDiv_147_35_15.D2 (m := 1) from colCertDiv_147_35_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_35_15_match


theorem leaf_147_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T147_35
      hfix147_35 hinj147_35 hcardT147_35
      (fun i => conj_mem_of_fixedPoints _ _ (T147_35 i) (hfix147_35 i) _)
      ⟨147, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T147_35_2 Q2.hfix147_35_2 Q2.hinj147_35_2
      Q2.hcardT147_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_35_2 i) (Q2.hfix147_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T147_35 = colFn colCertDiv_147_35_20.D1 (m := 1) from colCertDiv_147_35_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 20 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T147_35_2 = colFn colCertDiv_147_35_20.D2 (m := 1) from colCertDiv_147_35_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_35_20_match


theorem leaf_147_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T147_36
      hfix147_36 hinj147_36 hcardT147_36
      (fun i => conj_mem_of_fixedPoints _ _ (T147_36 i) (hfix147_36 i) _)
      ⟨147, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T147_36_2 Q2.hfix147_36_2 Q2.hinj147_36_2
      Q2.hcardT147_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_36_2 i) (Q2.hfix147_36_2 i) _)
      colCert_147_36_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T147_36
      hfix147_36 hinj147_36 hcardT147_36
      (fun i => conj_mem_of_fixedPoints _ _ (T147_36 i) (hfix147_36 i) _)
      ⟨147, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T147_36_2 Q2.hfix147_36_2 Q2.hinj147_36_2
      Q2.hcardT147_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_36_2 i) (Q2.hfix147_36_2 i) _)
      colCert_147_36_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T147_36
      hfix147_36 hinj147_36 hcardT147_36
      (fun i => conj_mem_of_fixedPoints _ _ (T147_36 i) (hfix147_36 i) _)
      ⟨147, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T147_36_2 Q2.hfix147_36_2 Q2.hinj147_36_2
      Q2.hcardT147_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_36_2 i) (Q2.hfix147_36_2 i) _)
      colCert_147_36_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T147_36
      hfix147_36 hinj147_36 hcardT147_36
      (fun i => conj_mem_of_fixedPoints _ _ (T147_36 i) (hfix147_36 i) _)
      ⟨147, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T147_36_2 Q2.hfix147_36_2 Q2.hinj147_36_2
      Q2.hcardT147_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_36_2 i) (Q2.hfix147_36_2 i) _)
      colCert_147_36_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T147_36
      hfix147_36 hinj147_36 hcardT147_36
      (fun i => conj_mem_of_fixedPoints _ _ (T147_36 i) (hfix147_36 i) _)
      ⟨147, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T147_36_2 Q2.hfix147_36_2 Q2.hinj147_36_2
      Q2.hcardT147_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_36_2 i) (Q2.hfix147_36_2 i) _)
      colCert_147_36_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T147_36
      hfix147_36 hinj147_36 hcardT147_36
      (fun i => conj_mem_of_fixedPoints _ _ (T147_36 i) (hfix147_36 i) _)
      ⟨147, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T147_36_2 Q2.hfix147_36_2 Q2.hinj147_36_2
      Q2.hcardT147_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_36_2 i) (Q2.hfix147_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T147_36 = colFn colCertDiv_147_36_5.D1 (m := 1) from colCertDiv_147_36_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 5 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T147_36_2 = colFn colCertDiv_147_36_5.D2 (m := 1) from colCertDiv_147_36_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_36_5_match


theorem leaf_147_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T147_36
      hfix147_36 hinj147_36 hcardT147_36
      (fun i => conj_mem_of_fixedPoints _ _ (T147_36 i) (hfix147_36 i) _)
      ⟨147, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T147_36_2 Q2.hfix147_36_2 Q2.hinj147_36_2
      Q2.hcardT147_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_36_2 i) (Q2.hfix147_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T147_36 = colFn colCertDiv_147_36_10.D1 (m := 1) from colCertDiv_147_36_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 10 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T147_36_2 = colFn colCertDiv_147_36_10.D2 (m := 1) from colCertDiv_147_36_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_36_10_match


theorem leaf_147_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T147_36
      hfix147_36 hinj147_36 hcardT147_36
      (fun i => conj_mem_of_fixedPoints _ _ (T147_36 i) (hfix147_36 i) _)
      ⟨147, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T147_36_2 Q2.hfix147_36_2 Q2.hinj147_36_2
      Q2.hcardT147_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_36_2 i) (Q2.hfix147_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T147_36 = colFn colCertDiv_147_36_15.D1 (m := 1) from colCertDiv_147_36_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 15 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T147_36_2 = colFn colCertDiv_147_36_15.D2 (m := 1) from colCertDiv_147_36_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_36_15_match


theorem leaf_147_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T147_36
      hfix147_36 hinj147_36 hcardT147_36
      (fun i => conj_mem_of_fixedPoints _ _ (T147_36 i) (hfix147_36 i) _)
      ⟨147, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T147_36_2 Q2.hfix147_36_2 Q2.hinj147_36_2
      Q2.hcardT147_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_36_2 i) (Q2.hfix147_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T147_36 = colFn colCertDiv_147_36_20.D1 (m := 1) from colCertDiv_147_36_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 20 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T147_36_2 = colFn colCertDiv_147_36_20.D2 (m := 1) from colCertDiv_147_36_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_36_20_match


theorem leaf_147_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T147_37
      hfix147_37 hinj147_37 hcardT147_37
      (fun i => conj_mem_of_fixedPoints _ _ (T147_37 i) (hfix147_37 i) _)
      ⟨147, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T147_37_2 Q2.hfix147_37_2 Q2.hinj147_37_2
      Q2.hcardT147_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_37_2 i) (Q2.hfix147_37_2 i) _)
      colCert_147_37_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T147_37
      hfix147_37 hinj147_37 hcardT147_37
      (fun i => conj_mem_of_fixedPoints _ _ (T147_37 i) (hfix147_37 i) _)
      ⟨147, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T147_37_2 Q2.hfix147_37_2 Q2.hinj147_37_2
      Q2.hcardT147_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_37_2 i) (Q2.hfix147_37_2 i) _)
      colCert_147_37_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T147_37
      hfix147_37 hinj147_37 hcardT147_37
      (fun i => conj_mem_of_fixedPoints _ _ (T147_37 i) (hfix147_37 i) _)
      ⟨147, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T147_37_2 Q2.hfix147_37_2 Q2.hinj147_37_2
      Q2.hcardT147_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_37_2 i) (Q2.hfix147_37_2 i) _)
      colCert_147_37_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T147_37
      hfix147_37 hinj147_37 hcardT147_37
      (fun i => conj_mem_of_fixedPoints _ _ (T147_37 i) (hfix147_37 i) _)
      ⟨147, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T147_37_2 Q2.hfix147_37_2 Q2.hinj147_37_2
      Q2.hcardT147_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_37_2 i) (Q2.hfix147_37_2 i) _)
      colCert_147_37_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T147_37
      hfix147_37 hinj147_37 hcardT147_37
      (fun i => conj_mem_of_fixedPoints _ _ (T147_37 i) (hfix147_37 i) _)
      ⟨147, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T147_37_2 Q2.hfix147_37_2 Q2.hinj147_37_2
      Q2.hcardT147_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_37_2 i) (Q2.hfix147_37_2 i) _)
      colCert_147_37_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T147_37
      hfix147_37 hinj147_37 hcardT147_37
      (fun i => conj_mem_of_fixedPoints _ _ (T147_37 i) (hfix147_37 i) _)
      ⟨147, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T147_37_2 Q2.hfix147_37_2 Q2.hinj147_37_2
      Q2.hcardT147_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_37_2 i) (Q2.hfix147_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T147_37 = colFn colCertDiv_147_37_5.D1 (m := 1) from colCertDiv_147_37_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T147_37_2 = colFn colCertDiv_147_37_5.D2 (m := 1) from colCertDiv_147_37_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_37_5_match


theorem leaf_147_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T147_37
      hfix147_37 hinj147_37 hcardT147_37
      (fun i => conj_mem_of_fixedPoints _ _ (T147_37 i) (hfix147_37 i) _)
      ⟨147, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T147_37_2 Q2.hfix147_37_2 Q2.hinj147_37_2
      Q2.hcardT147_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_37_2 i) (Q2.hfix147_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T147_37 = colFn colCertDiv_147_37_10.D1 (m := 1) from colCertDiv_147_37_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T147_37_2 = colFn colCertDiv_147_37_10.D2 (m := 1) from colCertDiv_147_37_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_37_10_match


theorem leaf_147_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T147_37
      hfix147_37 hinj147_37 hcardT147_37
      (fun i => conj_mem_of_fixedPoints _ _ (T147_37 i) (hfix147_37 i) _)
      ⟨147, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T147_37_2 Q2.hfix147_37_2 Q2.hinj147_37_2
      Q2.hcardT147_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_37_2 i) (Q2.hfix147_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T147_37 = colFn colCertDiv_147_37_15.D1 (m := 1) from colCertDiv_147_37_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T147_37_2 = colFn colCertDiv_147_37_15.D2 (m := 1) from colCertDiv_147_37_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_37_15_match


theorem leaf_147_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T147_37
      hfix147_37 hinj147_37 hcardT147_37
      (fun i => conj_mem_of_fixedPoints _ _ (T147_37 i) (hfix147_37 i) _)
      ⟨147, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T147_37_2 Q2.hfix147_37_2 Q2.hinj147_37_2
      Q2.hcardT147_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_37_2 i) (Q2.hfix147_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T147_37 = colFn colCertDiv_147_37_20.D1 (m := 1) from colCertDiv_147_37_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T147_37_2 = colFn colCertDiv_147_37_20.D2 (m := 1) from colCertDiv_147_37_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_37_20_match


theorem leaf_147_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T147_38
      hfix147_38 hinj147_38 hcardT147_38
      (fun i => conj_mem_of_fixedPoints _ _ (T147_38 i) (hfix147_38 i) _)
      ⟨147, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T147_38_2 Q2.hfix147_38_2 Q2.hinj147_38_2
      Q2.hcardT147_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_38_2 i) (Q2.hfix147_38_2 i) _)
      colCert_147_38_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T147_38
      hfix147_38 hinj147_38 hcardT147_38
      (fun i => conj_mem_of_fixedPoints _ _ (T147_38 i) (hfix147_38 i) _)
      ⟨147, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T147_38_2 Q2.hfix147_38_2 Q2.hinj147_38_2
      Q2.hcardT147_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_38_2 i) (Q2.hfix147_38_2 i) _)
      colCert_147_38_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T147_38
      hfix147_38 hinj147_38 hcardT147_38
      (fun i => conj_mem_of_fixedPoints _ _ (T147_38 i) (hfix147_38 i) _)
      ⟨147, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T147_38_2 Q2.hfix147_38_2 Q2.hinj147_38_2
      Q2.hcardT147_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_38_2 i) (Q2.hfix147_38_2 i) _)
      colCert_147_38_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T147_38
      hfix147_38 hinj147_38 hcardT147_38
      (fun i => conj_mem_of_fixedPoints _ _ (T147_38 i) (hfix147_38 i) _)
      ⟨147, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T147_38_2 Q2.hfix147_38_2 Q2.hinj147_38_2
      Q2.hcardT147_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_38_2 i) (Q2.hfix147_38_2 i) _)
      colCert_147_38_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T147_38
      hfix147_38 hinj147_38 hcardT147_38
      (fun i => conj_mem_of_fixedPoints _ _ (T147_38 i) (hfix147_38 i) _)
      ⟨147, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T147_38_2 Q2.hfix147_38_2 Q2.hinj147_38_2
      Q2.hcardT147_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_38_2 i) (Q2.hfix147_38_2 i) _)
      colCert_147_38_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T147_38
      hfix147_38 hinj147_38 hcardT147_38
      (fun i => conj_mem_of_fixedPoints _ _ (T147_38 i) (hfix147_38 i) _)
      ⟨147, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T147_38_2 Q2.hfix147_38_2 Q2.hinj147_38_2
      Q2.hcardT147_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_38_2 i) (Q2.hfix147_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T147_38 = colFn colCertDiv_147_38_5.D1 (m := 1) from colCertDiv_147_38_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T147_38_2 = colFn colCertDiv_147_38_5.D2 (m := 1) from colCertDiv_147_38_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_38_5_match


theorem leaf_147_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T147_38
      hfix147_38 hinj147_38 hcardT147_38
      (fun i => conj_mem_of_fixedPoints _ _ (T147_38 i) (hfix147_38 i) _)
      ⟨147, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T147_38_2 Q2.hfix147_38_2 Q2.hinj147_38_2
      Q2.hcardT147_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_38_2 i) (Q2.hfix147_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T147_38 = colFn colCertDiv_147_38_10.D1 (m := 1) from colCertDiv_147_38_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T147_38_2 = colFn colCertDiv_147_38_10.D2 (m := 1) from colCertDiv_147_38_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_38_10_match


theorem leaf_147_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T147_38
      hfix147_38 hinj147_38 hcardT147_38
      (fun i => conj_mem_of_fixedPoints _ _ (T147_38 i) (hfix147_38 i) _)
      ⟨147, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T147_38_2 Q2.hfix147_38_2 Q2.hinj147_38_2
      Q2.hcardT147_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_38_2 i) (Q2.hfix147_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T147_38 = colFn colCertDiv_147_38_15.D1 (m := 1) from colCertDiv_147_38_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T147_38_2 = colFn colCertDiv_147_38_15.D2 (m := 1) from colCertDiv_147_38_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_38_15_match


theorem leaf_147_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T147_38
      hfix147_38 hinj147_38 hcardT147_38
      (fun i => conj_mem_of_fixedPoints _ _ (T147_38 i) (hfix147_38 i) _)
      ⟨147, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T147_38_2 Q2.hfix147_38_2 Q2.hinj147_38_2
      Q2.hcardT147_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_38_2 i) (Q2.hfix147_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T147_38 = colFn colCertDiv_147_38_20.D1 (m := 1) from colCertDiv_147_38_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T147_38_2 = colFn colCertDiv_147_38_20.D2 (m := 1) from colCertDiv_147_38_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_38_20_match


theorem leaf_147_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T147_39
      hfix147_39 hinj147_39 hcardT147_39
      (fun i => conj_mem_of_fixedPoints _ _ (T147_39 i) (hfix147_39 i) _)
      ⟨147, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T147_39_2 Q2.hfix147_39_2 Q2.hinj147_39_2
      Q2.hcardT147_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_39_2 i) (Q2.hfix147_39_2 i) _)
      colCert_147_39_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T147_39
      hfix147_39 hinj147_39 hcardT147_39
      (fun i => conj_mem_of_fixedPoints _ _ (T147_39 i) (hfix147_39 i) _)
      ⟨147, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T147_39_2 Q2.hfix147_39_2 Q2.hinj147_39_2
      Q2.hcardT147_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_39_2 i) (Q2.hfix147_39_2 i) _)
      colCert_147_39_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T147_39
      hfix147_39 hinj147_39 hcardT147_39
      (fun i => conj_mem_of_fixedPoints _ _ (T147_39 i) (hfix147_39 i) _)
      ⟨147, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T147_39_2 Q2.hfix147_39_2 Q2.hinj147_39_2
      Q2.hcardT147_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_39_2 i) (Q2.hfix147_39_2 i) _)
      colCert_147_39_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T147_39
      hfix147_39 hinj147_39 hcardT147_39
      (fun i => conj_mem_of_fixedPoints _ _ (T147_39 i) (hfix147_39 i) _)
      ⟨147, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T147_39_2 Q2.hfix147_39_2 Q2.hinj147_39_2
      Q2.hcardT147_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_39_2 i) (Q2.hfix147_39_2 i) _)
      colCert_147_39_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T147_39
      hfix147_39 hinj147_39 hcardT147_39
      (fun i => conj_mem_of_fixedPoints _ _ (T147_39 i) (hfix147_39 i) _)
      ⟨147, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T147_39_2 Q2.hfix147_39_2 Q2.hinj147_39_2
      Q2.hcardT147_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_39_2 i) (Q2.hfix147_39_2 i) _)
      colCert_147_39_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T147_39
      hfix147_39 hinj147_39 hcardT147_39
      (fun i => conj_mem_of_fixedPoints _ _ (T147_39 i) (hfix147_39 i) _)
      ⟨147, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T147_39_2 Q2.hfix147_39_2 Q2.hinj147_39_2
      Q2.hcardT147_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_39_2 i) (Q2.hfix147_39_2 i) _)
      colCert_147_39_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T147_39
      hfix147_39 hinj147_39 hcardT147_39
      (fun i => conj_mem_of_fixedPoints _ _ (T147_39 i) (hfix147_39 i) _)
      ⟨147, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T147_39_2 Q2.hfix147_39_2 Q2.hinj147_39_2
      Q2.hcardT147_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_39_2 i) (Q2.hfix147_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T147_39 = colFn colCertDiv_147_39_10.D1 (m := 1) from colCertDiv_147_39_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 10 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T147_39_2 = colFn colCertDiv_147_39_10.D2 (m := 1) from colCertDiv_147_39_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_39_10_match


theorem leaf_147_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T147_39
      hfix147_39 hinj147_39 hcardT147_39
      (fun i => conj_mem_of_fixedPoints _ _ (T147_39 i) (hfix147_39 i) _)
      ⟨147, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T147_39_2 Q2.hfix147_39_2 Q2.hinj147_39_2
      Q2.hcardT147_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_39_2 i) (Q2.hfix147_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T147_39 = colFn colCertDiv_147_39_15.D1 (m := 1) from colCertDiv_147_39_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 15 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T147_39_2 = colFn colCertDiv_147_39_15.D2 (m := 1) from colCertDiv_147_39_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_39_15_match


theorem leaf_147_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T147_39
      hfix147_39 hinj147_39 hcardT147_39
      (fun i => conj_mem_of_fixedPoints _ _ (T147_39 i) (hfix147_39 i) _)
      ⟨147, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T147_39_2 Q2.hfix147_39_2 Q2.hinj147_39_2
      Q2.hcardT147_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_39_2 i) (Q2.hfix147_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T147_39 = colFn colCertDiv_147_39_20.D1 (m := 1) from colCertDiv_147_39_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 20 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T147_39_2 = colFn colCertDiv_147_39_20.D2 (m := 1) from colCertDiv_147_39_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_39_20_match


theorem leaf_147_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T147_40
      hfix147_40 hinj147_40 hcardT147_40
      (fun i => conj_mem_of_fixedPoints _ _ (T147_40 i) (hfix147_40 i) _)
      ⟨147, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T147_40_2 Q2.hfix147_40_2 Q2.hinj147_40_2
      Q2.hcardT147_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_40_2 i) (Q2.hfix147_40_2 i) _)
      colCert_147_40_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T147_40
      hfix147_40 hinj147_40 hcardT147_40
      (fun i => conj_mem_of_fixedPoints _ _ (T147_40 i) (hfix147_40 i) _)
      ⟨147, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T147_40_2 Q2.hfix147_40_2 Q2.hinj147_40_2
      Q2.hcardT147_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_40_2 i) (Q2.hfix147_40_2 i) _)
      colCert_147_40_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T147_40
      hfix147_40 hinj147_40 hcardT147_40
      (fun i => conj_mem_of_fixedPoints _ _ (T147_40 i) (hfix147_40 i) _)
      ⟨147, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T147_40_2 Q2.hfix147_40_2 Q2.hinj147_40_2
      Q2.hcardT147_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_40_2 i) (Q2.hfix147_40_2 i) _)
      colCert_147_40_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T147_40
      hfix147_40 hinj147_40 hcardT147_40
      (fun i => conj_mem_of_fixedPoints _ _ (T147_40 i) (hfix147_40 i) _)
      ⟨147, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T147_40_2 Q2.hfix147_40_2 Q2.hinj147_40_2
      Q2.hcardT147_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_40_2 i) (Q2.hfix147_40_2 i) _)
      colCert_147_40_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T147_40
      hfix147_40 hinj147_40 hcardT147_40
      (fun i => conj_mem_of_fixedPoints _ _ (T147_40 i) (hfix147_40 i) _)
      ⟨147, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T147_40_2 Q2.hfix147_40_2 Q2.hinj147_40_2
      Q2.hcardT147_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_40_2 i) (Q2.hfix147_40_2 i) _)
      colCert_147_40_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T147_40
      hfix147_40 hinj147_40 hcardT147_40
      (fun i => conj_mem_of_fixedPoints _ _ (T147_40 i) (hfix147_40 i) _)
      ⟨147, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T147_40_2 Q2.hfix147_40_2 Q2.hinj147_40_2
      Q2.hcardT147_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_40_2 i) (Q2.hfix147_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T147_40 = colFn colCertDiv_147_40_5.D1 (m := 1) from colCertDiv_147_40_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 5 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T147_40_2 = colFn colCertDiv_147_40_5.D2 (m := 1) from colCertDiv_147_40_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_40_5_match


theorem leaf_147_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T147_40
      hfix147_40 hinj147_40 hcardT147_40
      (fun i => conj_mem_of_fixedPoints _ _ (T147_40 i) (hfix147_40 i) _)
      ⟨147, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T147_40_2 Q2.hfix147_40_2 Q2.hinj147_40_2
      Q2.hcardT147_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_40_2 i) (Q2.hfix147_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T147_40 = colFn colCertDiv_147_40_10.D1 (m := 1) from colCertDiv_147_40_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 10 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T147_40_2 = colFn colCertDiv_147_40_10.D2 (m := 1) from colCertDiv_147_40_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_40_10_match


theorem leaf_147_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T147_40
      hfix147_40 hinj147_40 hcardT147_40
      (fun i => conj_mem_of_fixedPoints _ _ (T147_40 i) (hfix147_40 i) _)
      ⟨147, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T147_40_2 Q2.hfix147_40_2 Q2.hinj147_40_2
      Q2.hcardT147_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_40_2 i) (Q2.hfix147_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T147_40 = colFn colCertDiv_147_40_15.D1 (m := 1) from colCertDiv_147_40_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 15 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T147_40_2 = colFn colCertDiv_147_40_15.D2 (m := 1) from colCertDiv_147_40_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_40_15_match


theorem leaf_147_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T147_40
      hfix147_40 hinj147_40 hcardT147_40
      (fun i => conj_mem_of_fixedPoints _ _ (T147_40 i) (hfix147_40 i) _)
      ⟨147, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T147_40_2 Q2.hfix147_40_2 Q2.hinj147_40_2
      Q2.hcardT147_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_40_2 i) (Q2.hfix147_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T147_40 = colFn colCertDiv_147_40_20.D1 (m := 1) from colCertDiv_147_40_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 20 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T147_40_2 = colFn colCertDiv_147_40_20.D2 (m := 1) from colCertDiv_147_40_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_40_20_match


theorem leaf_147_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T147_41
      hfix147_41 hinj147_41 hcardT147_41
      (fun i => conj_mem_of_fixedPoints _ _ (T147_41 i) (hfix147_41 i) _)
      ⟨147, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T147_41_2 Q2.hfix147_41_2 Q2.hinj147_41_2
      Q2.hcardT147_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_41_2 i) (Q2.hfix147_41_2 i) _)
      colCert_147_41_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T147_41
      hfix147_41 hinj147_41 hcardT147_41
      (fun i => conj_mem_of_fixedPoints _ _ (T147_41 i) (hfix147_41 i) _)
      ⟨147, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T147_41_2 Q2.hfix147_41_2 Q2.hinj147_41_2
      Q2.hcardT147_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_41_2 i) (Q2.hfix147_41_2 i) _)
      colCert_147_41_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T147_41
      hfix147_41 hinj147_41 hcardT147_41
      (fun i => conj_mem_of_fixedPoints _ _ (T147_41 i) (hfix147_41 i) _)
      ⟨147, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T147_41_2 Q2.hfix147_41_2 Q2.hinj147_41_2
      Q2.hcardT147_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_41_2 i) (Q2.hfix147_41_2 i) _)
      colCert_147_41_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T147_41
      hfix147_41 hinj147_41 hcardT147_41
      (fun i => conj_mem_of_fixedPoints _ _ (T147_41 i) (hfix147_41 i) _)
      ⟨147, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T147_41_2 Q2.hfix147_41_2 Q2.hinj147_41_2
      Q2.hcardT147_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_41_2 i) (Q2.hfix147_41_2 i) _)
      colCert_147_41_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T147_41
      hfix147_41 hinj147_41 hcardT147_41
      (fun i => conj_mem_of_fixedPoints _ _ (T147_41 i) (hfix147_41 i) _)
      ⟨147, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T147_41_2 Q2.hfix147_41_2 Q2.hinj147_41_2
      Q2.hcardT147_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_41_2 i) (Q2.hfix147_41_2 i) _)
      colCert_147_41_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T147_41
      hfix147_41 hinj147_41 hcardT147_41
      (fun i => conj_mem_of_fixedPoints _ _ (T147_41 i) (hfix147_41 i) _)
      ⟨147, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T147_41_2 Q2.hfix147_41_2 Q2.hinj147_41_2
      Q2.hcardT147_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_41_2 i) (Q2.hfix147_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T147_41 = colFn colCertDiv_147_41_5.D1 (m := 1) from colCertDiv_147_41_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 5 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T147_41_2 = colFn colCertDiv_147_41_5.D2 (m := 1) from colCertDiv_147_41_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_41_5_match


theorem leaf_147_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T147_41
      hfix147_41 hinj147_41 hcardT147_41
      (fun i => conj_mem_of_fixedPoints _ _ (T147_41 i) (hfix147_41 i) _)
      ⟨147, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T147_41_2 Q2.hfix147_41_2 Q2.hinj147_41_2
      Q2.hcardT147_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_41_2 i) (Q2.hfix147_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T147_41 = colFn colCertDiv_147_41_10.D1 (m := 1) from colCertDiv_147_41_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 10 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T147_41_2 = colFn colCertDiv_147_41_10.D2 (m := 1) from colCertDiv_147_41_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_41_10_match


theorem leaf_147_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T147_41
      hfix147_41 hinj147_41 hcardT147_41
      (fun i => conj_mem_of_fixedPoints _ _ (T147_41 i) (hfix147_41 i) _)
      ⟨147, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T147_41_2 Q2.hfix147_41_2 Q2.hinj147_41_2
      Q2.hcardT147_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_41_2 i) (Q2.hfix147_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T147_41 = colFn colCertDiv_147_41_15.D1 (m := 1) from colCertDiv_147_41_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 15 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T147_41_2 = colFn colCertDiv_147_41_15.D2 (m := 1) from colCertDiv_147_41_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_41_15_match


theorem leaf_147_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T147_41
      hfix147_41 hinj147_41 hcardT147_41
      (fun i => conj_mem_of_fixedPoints _ _ (T147_41 i) (hfix147_41 i) _)
      ⟨147, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T147_41_2 Q2.hfix147_41_2 Q2.hinj147_41_2
      Q2.hcardT147_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_41_2 i) (Q2.hfix147_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T147_41 = colFn colCertDiv_147_41_20.D1 (m := 1) from colCertDiv_147_41_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 20 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T147_41_2 = colFn colCertDiv_147_41_20.D2 (m := 1) from colCertDiv_147_41_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_41_20_match


theorem leaf_147_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T147_42
      hfix147_42 hinj147_42 hcardT147_42
      (fun i => conj_mem_of_fixedPoints _ _ (T147_42 i) (hfix147_42 i) _)
      ⟨147, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T147_42_2 Q2.hfix147_42_2 Q2.hinj147_42_2
      Q2.hcardT147_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_42_2 i) (Q2.hfix147_42_2 i) _)
      colCert_147_42_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T147_42
      hfix147_42 hinj147_42 hcardT147_42
      (fun i => conj_mem_of_fixedPoints _ _ (T147_42 i) (hfix147_42 i) _)
      ⟨147, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T147_42_2 Q2.hfix147_42_2 Q2.hinj147_42_2
      Q2.hcardT147_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_42_2 i) (Q2.hfix147_42_2 i) _)
      colCert_147_42_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T147_42
      hfix147_42 hinj147_42 hcardT147_42
      (fun i => conj_mem_of_fixedPoints _ _ (T147_42 i) (hfix147_42 i) _)
      ⟨147, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T147_42_2 Q2.hfix147_42_2 Q2.hinj147_42_2
      Q2.hcardT147_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_42_2 i) (Q2.hfix147_42_2 i) _)
      colCert_147_42_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T147_42
      hfix147_42 hinj147_42 hcardT147_42
      (fun i => conj_mem_of_fixedPoints _ _ (T147_42 i) (hfix147_42 i) _)
      ⟨147, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T147_42_2 Q2.hfix147_42_2 Q2.hinj147_42_2
      Q2.hcardT147_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_42_2 i) (Q2.hfix147_42_2 i) _)
      colCert_147_42_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T147_42
      hfix147_42 hinj147_42 hcardT147_42
      (fun i => conj_mem_of_fixedPoints _ _ (T147_42 i) (hfix147_42 i) _)
      ⟨147, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T147_42_2 Q2.hfix147_42_2 Q2.hinj147_42_2
      Q2.hcardT147_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_42_2 i) (Q2.hfix147_42_2 i) _)
      colCert_147_42_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T147_42
      hfix147_42 hinj147_42 hcardT147_42
      (fun i => conj_mem_of_fixedPoints _ _ (T147_42 i) (hfix147_42 i) _)
      ⟨147, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T147_42_2 Q2.hfix147_42_2 Q2.hinj147_42_2
      Q2.hcardT147_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_42_2 i) (Q2.hfix147_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T147_42 = colFn colCertDiv_147_42_5.D1 (m := 1) from colCertDiv_147_42_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T147_42_2 = colFn colCertDiv_147_42_5.D2 (m := 1) from colCertDiv_147_42_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_42_5_match


theorem leaf_147_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T147_42
      hfix147_42 hinj147_42 hcardT147_42
      (fun i => conj_mem_of_fixedPoints _ _ (T147_42 i) (hfix147_42 i) _)
      ⟨147, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T147_42_2 Q2.hfix147_42_2 Q2.hinj147_42_2
      Q2.hcardT147_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_42_2 i) (Q2.hfix147_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T147_42 = colFn colCertDiv_147_42_10.D1 (m := 1) from colCertDiv_147_42_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T147_42_2 = colFn colCertDiv_147_42_10.D2 (m := 1) from colCertDiv_147_42_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_42_10_match


theorem leaf_147_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T147_42
      hfix147_42 hinj147_42 hcardT147_42
      (fun i => conj_mem_of_fixedPoints _ _ (T147_42 i) (hfix147_42 i) _)
      ⟨147, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T147_42_2 Q2.hfix147_42_2 Q2.hinj147_42_2
      Q2.hcardT147_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_42_2 i) (Q2.hfix147_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T147_42 = colFn colCertDiv_147_42_15.D1 (m := 1) from colCertDiv_147_42_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T147_42_2 = colFn colCertDiv_147_42_15.D2 (m := 1) from colCertDiv_147_42_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_42_15_match


theorem leaf_147_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T147_42
      hfix147_42 hinj147_42 hcardT147_42
      (fun i => conj_mem_of_fixedPoints _ _ (T147_42 i) (hfix147_42 i) _)
      ⟨147, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T147_42_2 Q2.hfix147_42_2 Q2.hinj147_42_2
      Q2.hcardT147_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_42_2 i) (Q2.hfix147_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T147_42 = colFn colCertDiv_147_42_20.D1 (m := 1) from colCertDiv_147_42_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T147_42_2 = colFn colCertDiv_147_42_20.D2 (m := 1) from colCertDiv_147_42_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_42_20_match


theorem leaf_147_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T147_43
      hfix147_43 hinj147_43 hcardT147_43
      (fun i => conj_mem_of_fixedPoints _ _ (T147_43 i) (hfix147_43 i) _)
      ⟨147, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T147_43_2 Q2.hfix147_43_2 Q2.hinj147_43_2
      Q2.hcardT147_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_43_2 i) (Q2.hfix147_43_2 i) _)
      colCert_147_43_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T147_43
      hfix147_43 hinj147_43 hcardT147_43
      (fun i => conj_mem_of_fixedPoints _ _ (T147_43 i) (hfix147_43 i) _)
      ⟨147, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T147_43_2 Q2.hfix147_43_2 Q2.hinj147_43_2
      Q2.hcardT147_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_43_2 i) (Q2.hfix147_43_2 i) _)
      colCert_147_43_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T147_43
      hfix147_43 hinj147_43 hcardT147_43
      (fun i => conj_mem_of_fixedPoints _ _ (T147_43 i) (hfix147_43 i) _)
      ⟨147, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T147_43_2 Q2.hfix147_43_2 Q2.hinj147_43_2
      Q2.hcardT147_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_43_2 i) (Q2.hfix147_43_2 i) _)
      colCert_147_43_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T147_43
      hfix147_43 hinj147_43 hcardT147_43
      (fun i => conj_mem_of_fixedPoints _ _ (T147_43 i) (hfix147_43 i) _)
      ⟨147, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T147_43_2 Q2.hfix147_43_2 Q2.hinj147_43_2
      Q2.hcardT147_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_43_2 i) (Q2.hfix147_43_2 i) _)
      colCert_147_43_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T147_43
      hfix147_43 hinj147_43 hcardT147_43
      (fun i => conj_mem_of_fixedPoints _ _ (T147_43 i) (hfix147_43 i) _)
      ⟨147, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T147_43_2 Q2.hfix147_43_2 Q2.hinj147_43_2
      Q2.hcardT147_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_43_2 i) (Q2.hfix147_43_2 i) _)
      colCert_147_43_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T147_43
      hfix147_43 hinj147_43 hcardT147_43
      (fun i => conj_mem_of_fixedPoints _ _ (T147_43 i) (hfix147_43 i) _)
      ⟨147, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T147_43_2 Q2.hfix147_43_2 Q2.hinj147_43_2
      Q2.hcardT147_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_43_2 i) (Q2.hfix147_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T147_43 = colFn colCertDiv_147_43_5.D1 (m := 1) from colCertDiv_147_43_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T147_43_2 = colFn colCertDiv_147_43_5.D2 (m := 1) from colCertDiv_147_43_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_43_5_match


theorem leaf_147_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T147_43
      hfix147_43 hinj147_43 hcardT147_43
      (fun i => conj_mem_of_fixedPoints _ _ (T147_43 i) (hfix147_43 i) _)
      ⟨147, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T147_43_2 Q2.hfix147_43_2 Q2.hinj147_43_2
      Q2.hcardT147_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_43_2 i) (Q2.hfix147_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T147_43 = colFn colCertDiv_147_43_10.D1 (m := 1) from colCertDiv_147_43_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T147_43_2 = colFn colCertDiv_147_43_10.D2 (m := 1) from colCertDiv_147_43_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_43_10_match


theorem leaf_147_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T147_43
      hfix147_43 hinj147_43 hcardT147_43
      (fun i => conj_mem_of_fixedPoints _ _ (T147_43 i) (hfix147_43 i) _)
      ⟨147, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T147_43_2 Q2.hfix147_43_2 Q2.hinj147_43_2
      Q2.hcardT147_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_43_2 i) (Q2.hfix147_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T147_43 = colFn colCertDiv_147_43_15.D1 (m := 1) from colCertDiv_147_43_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T147_43_2 = colFn colCertDiv_147_43_15.D2 (m := 1) from colCertDiv_147_43_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_43_15_match


theorem leaf_147_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T147_43
      hfix147_43 hinj147_43 hcardT147_43
      (fun i => conj_mem_of_fixedPoints _ _ (T147_43 i) (hfix147_43 i) _)
      ⟨147, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T147_43_2 Q2.hfix147_43_2 Q2.hinj147_43_2
      Q2.hcardT147_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_43_2 i) (Q2.hfix147_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T147_43 = colFn colCertDiv_147_43_20.D1 (m := 1) from colCertDiv_147_43_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T147_43_2 = colFn colCertDiv_147_43_20.D2 (m := 1) from colCertDiv_147_43_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_43_20_match


theorem leaf_147_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T147_44
      hfix147_44 hinj147_44 hcardT147_44
      (fun i => conj_mem_of_fixedPoints _ _ (T147_44 i) (hfix147_44 i) _)
      ⟨147, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T147_44_2 Q2.hfix147_44_2 Q2.hinj147_44_2
      Q2.hcardT147_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_44_2 i) (Q2.hfix147_44_2 i) _)
      colCert_147_44_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T147_44
      hfix147_44 hinj147_44 hcardT147_44
      (fun i => conj_mem_of_fixedPoints _ _ (T147_44 i) (hfix147_44 i) _)
      ⟨147, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T147_44_2 Q2.hfix147_44_2 Q2.hinj147_44_2
      Q2.hcardT147_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_44_2 i) (Q2.hfix147_44_2 i) _)
      colCert_147_44_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T147_44
      hfix147_44 hinj147_44 hcardT147_44
      (fun i => conj_mem_of_fixedPoints _ _ (T147_44 i) (hfix147_44 i) _)
      ⟨147, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T147_44_2 Q2.hfix147_44_2 Q2.hinj147_44_2
      Q2.hcardT147_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_44_2 i) (Q2.hfix147_44_2 i) _)
      colCert_147_44_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T147_44
      hfix147_44 hinj147_44 hcardT147_44
      (fun i => conj_mem_of_fixedPoints _ _ (T147_44 i) (hfix147_44 i) _)
      ⟨147, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T147_44_2 Q2.hfix147_44_2 Q2.hinj147_44_2
      Q2.hcardT147_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_44_2 i) (Q2.hfix147_44_2 i) _)
      colCert_147_44_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T147_44
      hfix147_44 hinj147_44 hcardT147_44
      (fun i => conj_mem_of_fixedPoints _ _ (T147_44 i) (hfix147_44 i) _)
      ⟨147, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T147_44_2 Q2.hfix147_44_2 Q2.hinj147_44_2
      Q2.hcardT147_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_44_2 i) (Q2.hfix147_44_2 i) _)
      colCert_147_44_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T147_44
      hfix147_44 hinj147_44 hcardT147_44
      (fun i => conj_mem_of_fixedPoints _ _ (T147_44 i) (hfix147_44 i) _)
      ⟨147, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T147_44_2 Q2.hfix147_44_2 Q2.hinj147_44_2
      Q2.hcardT147_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_44_2 i) (Q2.hfix147_44_2 i) _)
      colCert_147_44_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T147_44
      hfix147_44 hinj147_44 hcardT147_44
      (fun i => conj_mem_of_fixedPoints _ _ (T147_44 i) (hfix147_44 i) _)
      ⟨147, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T147_44_2 Q2.hfix147_44_2 Q2.hinj147_44_2
      Q2.hcardT147_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_44_2 i) (Q2.hfix147_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T147_44 = colFn colCertDiv_147_44_10.D1 (m := 1) from colCertDiv_147_44_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 10 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T147_44_2 = colFn colCertDiv_147_44_10.D2 (m := 1) from colCertDiv_147_44_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_44_10_match


theorem leaf_147_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T147_44
      hfix147_44 hinj147_44 hcardT147_44
      (fun i => conj_mem_of_fixedPoints _ _ (T147_44 i) (hfix147_44 i) _)
      ⟨147, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T147_44_2 Q2.hfix147_44_2 Q2.hinj147_44_2
      Q2.hcardT147_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_44_2 i) (Q2.hfix147_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T147_44 = colFn colCertDiv_147_44_15.D1 (m := 1) from colCertDiv_147_44_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 15 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T147_44_2 = colFn colCertDiv_147_44_15.D2 (m := 1) from colCertDiv_147_44_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_44_15_match


theorem leaf_147_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T147_44
      hfix147_44 hinj147_44 hcardT147_44
      (fun i => conj_mem_of_fixedPoints _ _ (T147_44 i) (hfix147_44 i) _)
      ⟨147, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T147_44_2 Q2.hfix147_44_2 Q2.hinj147_44_2
      Q2.hcardT147_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_44_2 i) (Q2.hfix147_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T147_44 = colFn colCertDiv_147_44_20.D1 (m := 1) from colCertDiv_147_44_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 20 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T147_44_2 = colFn colCertDiv_147_44_20.D2 (m := 1) from colCertDiv_147_44_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_44_20_match


theorem leaf_147_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T147_45
      hfix147_45 hinj147_45 hcardT147_45
      (fun i => conj_mem_of_fixedPoints _ _ (T147_45 i) (hfix147_45 i) _)
      ⟨147, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T147_45_2 Q2.hfix147_45_2 Q2.hinj147_45_2
      Q2.hcardT147_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_45_2 i) (Q2.hfix147_45_2 i) _)
      colCert_147_45_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T147_45
      hfix147_45 hinj147_45 hcardT147_45
      (fun i => conj_mem_of_fixedPoints _ _ (T147_45 i) (hfix147_45 i) _)
      ⟨147, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T147_45_2 Q2.hfix147_45_2 Q2.hinj147_45_2
      Q2.hcardT147_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_45_2 i) (Q2.hfix147_45_2 i) _)
      colCert_147_45_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T147_45
      hfix147_45 hinj147_45 hcardT147_45
      (fun i => conj_mem_of_fixedPoints _ _ (T147_45 i) (hfix147_45 i) _)
      ⟨147, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T147_45_2 Q2.hfix147_45_2 Q2.hinj147_45_2
      Q2.hcardT147_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_45_2 i) (Q2.hfix147_45_2 i) _)
      colCert_147_45_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T147_45
      hfix147_45 hinj147_45 hcardT147_45
      (fun i => conj_mem_of_fixedPoints _ _ (T147_45 i) (hfix147_45 i) _)
      ⟨147, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T147_45_2 Q2.hfix147_45_2 Q2.hinj147_45_2
      Q2.hcardT147_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_45_2 i) (Q2.hfix147_45_2 i) _)
      colCert_147_45_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T147_45
      hfix147_45 hinj147_45 hcardT147_45
      (fun i => conj_mem_of_fixedPoints _ _ (T147_45 i) (hfix147_45 i) _)
      ⟨147, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T147_45_2 Q2.hfix147_45_2 Q2.hinj147_45_2
      Q2.hcardT147_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_45_2 i) (Q2.hfix147_45_2 i) _)
      colCert_147_45_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T147_45
      hfix147_45 hinj147_45 hcardT147_45
      (fun i => conj_mem_of_fixedPoints _ _ (T147_45 i) (hfix147_45 i) _)
      ⟨147, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T147_45_2 Q2.hfix147_45_2 Q2.hinj147_45_2
      Q2.hcardT147_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_45_2 i) (Q2.hfix147_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T147_45 = colFn colCertDiv_147_45_5.D1 (m := 1) from colCertDiv_147_45_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 5 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T147_45_2 = colFn colCertDiv_147_45_5.D2 (m := 1) from colCertDiv_147_45_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_45_5_match


theorem leaf_147_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T147_45
      hfix147_45 hinj147_45 hcardT147_45
      (fun i => conj_mem_of_fixedPoints _ _ (T147_45 i) (hfix147_45 i) _)
      ⟨147, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T147_45_2 Q2.hfix147_45_2 Q2.hinj147_45_2
      Q2.hcardT147_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_45_2 i) (Q2.hfix147_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T147_45 = colFn colCertDiv_147_45_10.D1 (m := 1) from colCertDiv_147_45_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 10 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T147_45_2 = colFn colCertDiv_147_45_10.D2 (m := 1) from colCertDiv_147_45_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_45_10_match


theorem leaf_147_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T147_45
      hfix147_45 hinj147_45 hcardT147_45
      (fun i => conj_mem_of_fixedPoints _ _ (T147_45 i) (hfix147_45 i) _)
      ⟨147, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T147_45_2 Q2.hfix147_45_2 Q2.hinj147_45_2
      Q2.hcardT147_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_45_2 i) (Q2.hfix147_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T147_45 = colFn colCertDiv_147_45_15.D1 (m := 1) from colCertDiv_147_45_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 15 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T147_45_2 = colFn colCertDiv_147_45_15.D2 (m := 1) from colCertDiv_147_45_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_45_15_match


theorem leaf_147_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T147_45
      hfix147_45 hinj147_45 hcardT147_45
      (fun i => conj_mem_of_fixedPoints _ _ (T147_45 i) (hfix147_45 i) _)
      ⟨147, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T147_45_2 Q2.hfix147_45_2 Q2.hinj147_45_2
      Q2.hcardT147_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_45_2 i) (Q2.hfix147_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T147_45 = colFn colCertDiv_147_45_20.D1 (m := 1) from colCertDiv_147_45_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 20 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T147_45_2 = colFn colCertDiv_147_45_20.D2 (m := 1) from colCertDiv_147_45_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_45_20_match


theorem leaf_147_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T147_46
      hfix147_46 hinj147_46 hcardT147_46
      (fun i => conj_mem_of_fixedPoints _ _ (T147_46 i) (hfix147_46 i) _)
      ⟨147, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T147_46_2 Q2.hfix147_46_2 Q2.hinj147_46_2
      Q2.hcardT147_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_46_2 i) (Q2.hfix147_46_2 i) _)
      colCert_147_46_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T147_46
      hfix147_46 hinj147_46 hcardT147_46
      (fun i => conj_mem_of_fixedPoints _ _ (T147_46 i) (hfix147_46 i) _)
      ⟨147, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T147_46_2 Q2.hfix147_46_2 Q2.hinj147_46_2
      Q2.hcardT147_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_46_2 i) (Q2.hfix147_46_2 i) _)
      colCert_147_46_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T147_46
      hfix147_46 hinj147_46 hcardT147_46
      (fun i => conj_mem_of_fixedPoints _ _ (T147_46 i) (hfix147_46 i) _)
      ⟨147, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T147_46_2 Q2.hfix147_46_2 Q2.hinj147_46_2
      Q2.hcardT147_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_46_2 i) (Q2.hfix147_46_2 i) _)
      colCert_147_46_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T147_46
      hfix147_46 hinj147_46 hcardT147_46
      (fun i => conj_mem_of_fixedPoints _ _ (T147_46 i) (hfix147_46 i) _)
      ⟨147, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T147_46_2 Q2.hfix147_46_2 Q2.hinj147_46_2
      Q2.hcardT147_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_46_2 i) (Q2.hfix147_46_2 i) _)
      colCert_147_46_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T147_46
      hfix147_46 hinj147_46 hcardT147_46
      (fun i => conj_mem_of_fixedPoints _ _ (T147_46 i) (hfix147_46 i) _)
      ⟨147, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T147_46_2 Q2.hfix147_46_2 Q2.hinj147_46_2
      Q2.hcardT147_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_46_2 i) (Q2.hfix147_46_2 i) _)
      colCert_147_46_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T147_46
      hfix147_46 hinj147_46 hcardT147_46
      (fun i => conj_mem_of_fixedPoints _ _ (T147_46 i) (hfix147_46 i) _)
      ⟨147, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T147_46_2 Q2.hfix147_46_2 Q2.hinj147_46_2
      Q2.hcardT147_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_46_2 i) (Q2.hfix147_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T147_46 = colFn colCertDiv_147_46_5.D1 (m := 1) from colCertDiv_147_46_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 5 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T147_46_2 = colFn colCertDiv_147_46_5.D2 (m := 1) from colCertDiv_147_46_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_46_5_match


theorem leaf_147_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T147_46
      hfix147_46 hinj147_46 hcardT147_46
      (fun i => conj_mem_of_fixedPoints _ _ (T147_46 i) (hfix147_46 i) _)
      ⟨147, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T147_46_2 Q2.hfix147_46_2 Q2.hinj147_46_2
      Q2.hcardT147_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_46_2 i) (Q2.hfix147_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T147_46 = colFn colCertDiv_147_46_10.D1 (m := 1) from colCertDiv_147_46_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 10 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T147_46_2 = colFn colCertDiv_147_46_10.D2 (m := 1) from colCertDiv_147_46_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_46_10_match


theorem leaf_147_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T147_46
      hfix147_46 hinj147_46 hcardT147_46
      (fun i => conj_mem_of_fixedPoints _ _ (T147_46 i) (hfix147_46 i) _)
      ⟨147, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T147_46_2 Q2.hfix147_46_2 Q2.hinj147_46_2
      Q2.hcardT147_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_46_2 i) (Q2.hfix147_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T147_46 = colFn colCertDiv_147_46_15.D1 (m := 1) from colCertDiv_147_46_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 15 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T147_46_2 = colFn colCertDiv_147_46_15.D2 (m := 1) from colCertDiv_147_46_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_46_15_match


theorem leaf_147_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T147_46
      hfix147_46 hinj147_46 hcardT147_46
      (fun i => conj_mem_of_fixedPoints _ _ (T147_46 i) (hfix147_46 i) _)
      ⟨147, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T147_46_2 Q2.hfix147_46_2 Q2.hinj147_46_2
      Q2.hcardT147_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_46_2 i) (Q2.hfix147_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T147_46 = colFn colCertDiv_147_46_20.D1 (m := 1) from colCertDiv_147_46_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 20 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T147_46_2 = colFn colCertDiv_147_46_20.D2 (m := 1) from colCertDiv_147_46_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_46_20_match


theorem leaf_147_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T147_47
      hfix147_47 hinj147_47 hcardT147_47
      (fun i => conj_mem_of_fixedPoints _ _ (T147_47 i) (hfix147_47 i) _)
      ⟨147, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T147_47_2 Q2.hfix147_47_2 Q2.hinj147_47_2
      Q2.hcardT147_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_47_2 i) (Q2.hfix147_47_2 i) _)
      colCert_147_47_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T147_47
      hfix147_47 hinj147_47 hcardT147_47
      (fun i => conj_mem_of_fixedPoints _ _ (T147_47 i) (hfix147_47 i) _)
      ⟨147, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T147_47_2 Q2.hfix147_47_2 Q2.hinj147_47_2
      Q2.hcardT147_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_47_2 i) (Q2.hfix147_47_2 i) _)
      colCert_147_47_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T147_47
      hfix147_47 hinj147_47 hcardT147_47
      (fun i => conj_mem_of_fixedPoints _ _ (T147_47 i) (hfix147_47 i) _)
      ⟨147, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T147_47_2 Q2.hfix147_47_2 Q2.hinj147_47_2
      Q2.hcardT147_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_47_2 i) (Q2.hfix147_47_2 i) _)
      colCert_147_47_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T147_47
      hfix147_47 hinj147_47 hcardT147_47
      (fun i => conj_mem_of_fixedPoints _ _ (T147_47 i) (hfix147_47 i) _)
      ⟨147, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T147_47_2 Q2.hfix147_47_2 Q2.hinj147_47_2
      Q2.hcardT147_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_47_2 i) (Q2.hfix147_47_2 i) _)
      colCert_147_47_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T147_47
      hfix147_47 hinj147_47 hcardT147_47
      (fun i => conj_mem_of_fixedPoints _ _ (T147_47 i) (hfix147_47 i) _)
      ⟨147, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T147_47_2 Q2.hfix147_47_2 Q2.hinj147_47_2
      Q2.hcardT147_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_47_2 i) (Q2.hfix147_47_2 i) _)
      colCert_147_47_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T147_47
      hfix147_47 hinj147_47 hcardT147_47
      (fun i => conj_mem_of_fixedPoints _ _ (T147_47 i) (hfix147_47 i) _)
      ⟨147, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T147_47_2 Q2.hfix147_47_2 Q2.hinj147_47_2
      Q2.hcardT147_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_47_2 i) (Q2.hfix147_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T147_47 = colFn colCertDiv_147_47_5.D1 (m := 1) from colCertDiv_147_47_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T147_47_2 = colFn colCertDiv_147_47_5.D2 (m := 1) from colCertDiv_147_47_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_47_5_match


theorem leaf_147_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T147_47
      hfix147_47 hinj147_47 hcardT147_47
      (fun i => conj_mem_of_fixedPoints _ _ (T147_47 i) (hfix147_47 i) _)
      ⟨147, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T147_47_2 Q2.hfix147_47_2 Q2.hinj147_47_2
      Q2.hcardT147_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_47_2 i) (Q2.hfix147_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T147_47 = colFn colCertDiv_147_47_10.D1 (m := 1) from colCertDiv_147_47_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T147_47_2 = colFn colCertDiv_147_47_10.D2 (m := 1) from colCertDiv_147_47_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_47_10_match


theorem leaf_147_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T147_47
      hfix147_47 hinj147_47 hcardT147_47
      (fun i => conj_mem_of_fixedPoints _ _ (T147_47 i) (hfix147_47 i) _)
      ⟨147, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T147_47_2 Q2.hfix147_47_2 Q2.hinj147_47_2
      Q2.hcardT147_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_47_2 i) (Q2.hfix147_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T147_47 = colFn colCertDiv_147_47_15.D1 (m := 1) from colCertDiv_147_47_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T147_47_2 = colFn colCertDiv_147_47_15.D2 (m := 1) from colCertDiv_147_47_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_47_15_match


theorem leaf_147_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T147_47
      hfix147_47 hinj147_47 hcardT147_47
      (fun i => conj_mem_of_fixedPoints _ _ (T147_47 i) (hfix147_47 i) _)
      ⟨147, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T147_47_2 Q2.hfix147_47_2 Q2.hinj147_47_2
      Q2.hcardT147_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_47_2 i) (Q2.hfix147_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T147_47 = colFn colCertDiv_147_47_20.D1 (m := 1) from colCertDiv_147_47_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T147_47_2 = colFn colCertDiv_147_47_20.D2 (m := 1) from colCertDiv_147_47_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_47_20_match


theorem leaf_147_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T147_48
      hfix147_48 hinj147_48 hcardT147_48
      (fun i => conj_mem_of_fixedPoints _ _ (T147_48 i) (hfix147_48 i) _)
      ⟨147, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T147_48_2 Q2.hfix147_48_2 Q2.hinj147_48_2
      Q2.hcardT147_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_48_2 i) (Q2.hfix147_48_2 i) _)
      colCert_147_48_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T147_48
      hfix147_48 hinj147_48 hcardT147_48
      (fun i => conj_mem_of_fixedPoints _ _ (T147_48 i) (hfix147_48 i) _)
      ⟨147, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T147_48_2 Q2.hfix147_48_2 Q2.hinj147_48_2
      Q2.hcardT147_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_48_2 i) (Q2.hfix147_48_2 i) _)
      colCert_147_48_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T147_48
      hfix147_48 hinj147_48 hcardT147_48
      (fun i => conj_mem_of_fixedPoints _ _ (T147_48 i) (hfix147_48 i) _)
      ⟨147, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T147_48_2 Q2.hfix147_48_2 Q2.hinj147_48_2
      Q2.hcardT147_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_48_2 i) (Q2.hfix147_48_2 i) _)
      colCert_147_48_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T147_48
      hfix147_48 hinj147_48 hcardT147_48
      (fun i => conj_mem_of_fixedPoints _ _ (T147_48 i) (hfix147_48 i) _)
      ⟨147, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T147_48_2 Q2.hfix147_48_2 Q2.hinj147_48_2
      Q2.hcardT147_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_48_2 i) (Q2.hfix147_48_2 i) _)
      colCert_147_48_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T147_48
      hfix147_48 hinj147_48 hcardT147_48
      (fun i => conj_mem_of_fixedPoints _ _ (T147_48 i) (hfix147_48 i) _)
      ⟨147, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T147_48_2 Q2.hfix147_48_2 Q2.hinj147_48_2
      Q2.hcardT147_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_48_2 i) (Q2.hfix147_48_2 i) _)
      colCert_147_48_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T147_48
      hfix147_48 hinj147_48 hcardT147_48
      (fun i => conj_mem_of_fixedPoints _ _ (T147_48 i) (hfix147_48 i) _)
      ⟨147, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T147_48_2 Q2.hfix147_48_2 Q2.hinj147_48_2
      Q2.hcardT147_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_48_2 i) (Q2.hfix147_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T147_48 = colFn colCertDiv_147_48_5.D1 (m := 1) from colCertDiv_147_48_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T147_48_2 = colFn colCertDiv_147_48_5.D2 (m := 1) from colCertDiv_147_48_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_48_5_match


theorem leaf_147_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T147_48
      hfix147_48 hinj147_48 hcardT147_48
      (fun i => conj_mem_of_fixedPoints _ _ (T147_48 i) (hfix147_48 i) _)
      ⟨147, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T147_48_2 Q2.hfix147_48_2 Q2.hinj147_48_2
      Q2.hcardT147_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_48_2 i) (Q2.hfix147_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T147_48 = colFn colCertDiv_147_48_10.D1 (m := 1) from colCertDiv_147_48_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T147_48_2 = colFn colCertDiv_147_48_10.D2 (m := 1) from colCertDiv_147_48_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_48_10_match


theorem leaf_147_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T147_48
      hfix147_48 hinj147_48 hcardT147_48
      (fun i => conj_mem_of_fixedPoints _ _ (T147_48 i) (hfix147_48 i) _)
      ⟨147, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T147_48_2 Q2.hfix147_48_2 Q2.hinj147_48_2
      Q2.hcardT147_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_48_2 i) (Q2.hfix147_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T147_48 = colFn colCertDiv_147_48_15.D1 (m := 1) from colCertDiv_147_48_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T147_48_2 = colFn colCertDiv_147_48_15.D2 (m := 1) from colCertDiv_147_48_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_48_15_match


theorem leaf_147_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T147_48
      hfix147_48 hinj147_48 hcardT147_48
      (fun i => conj_mem_of_fixedPoints _ _ (T147_48 i) (hfix147_48 i) _)
      ⟨147, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T147_48_2 Q2.hfix147_48_2 Q2.hinj147_48_2
      Q2.hcardT147_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_48_2 i) (Q2.hfix147_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T147_48 = colFn colCertDiv_147_48_20.D1 (m := 1) from colCertDiv_147_48_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T147_48_2 = colFn colCertDiv_147_48_20.D2 (m := 1) from colCertDiv_147_48_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_48_20_match


theorem leaf_147_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T147_49
      hfix147_49 hinj147_49 hcardT147_49
      (fun i => conj_mem_of_fixedPoints _ _ (T147_49 i) (hfix147_49 i) _)
      ⟨147, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T147_49_2 Q2.hfix147_49_2 Q2.hinj147_49_2
      Q2.hcardT147_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_49_2 i) (Q2.hfix147_49_2 i) _)
      colCert_147_49_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T147_49
      hfix147_49 hinj147_49 hcardT147_49
      (fun i => conj_mem_of_fixedPoints _ _ (T147_49 i) (hfix147_49 i) _)
      ⟨147, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T147_49_2 Q2.hfix147_49_2 Q2.hinj147_49_2
      Q2.hcardT147_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_49_2 i) (Q2.hfix147_49_2 i) _)
      colCert_147_49_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T147_49
      hfix147_49 hinj147_49 hcardT147_49
      (fun i => conj_mem_of_fixedPoints _ _ (T147_49 i) (hfix147_49 i) _)
      ⟨147, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T147_49_2 Q2.hfix147_49_2 Q2.hinj147_49_2
      Q2.hcardT147_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_49_2 i) (Q2.hfix147_49_2 i) _)
      colCert_147_49_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T147_49
      hfix147_49 hinj147_49 hcardT147_49
      (fun i => conj_mem_of_fixedPoints _ _ (T147_49 i) (hfix147_49 i) _)
      ⟨147, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T147_49_2 Q2.hfix147_49_2 Q2.hinj147_49_2
      Q2.hcardT147_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_49_2 i) (Q2.hfix147_49_2 i) _)
      colCert_147_49_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T147_49
      hfix147_49 hinj147_49 hcardT147_49
      (fun i => conj_mem_of_fixedPoints _ _ (T147_49 i) (hfix147_49 i) _)
      ⟨147, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T147_49_2 Q2.hfix147_49_2 Q2.hinj147_49_2
      Q2.hcardT147_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_49_2 i) (Q2.hfix147_49_2 i) _)
      colCert_147_49_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T147_49
      hfix147_49 hinj147_49 hcardT147_49
      (fun i => conj_mem_of_fixedPoints _ _ (T147_49 i) (hfix147_49 i) _)
      ⟨147, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T147_49_2 Q2.hfix147_49_2 Q2.hinj147_49_2
      Q2.hcardT147_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_49_2 i) (Q2.hfix147_49_2 i) _)
      colCert_147_49_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T147_49
      hfix147_49 hinj147_49 hcardT147_49
      (fun i => conj_mem_of_fixedPoints _ _ (T147_49 i) (hfix147_49 i) _)
      ⟨147, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T147_49_2 Q2.hfix147_49_2 Q2.hinj147_49_2
      Q2.hcardT147_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_49_2 i) (Q2.hfix147_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T147_49 = colFn colCertDiv_147_49_10.D1 (m := 1) from colCertDiv_147_49_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 10 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T147_49_2 = colFn colCertDiv_147_49_10.D2 (m := 1) from colCertDiv_147_49_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_49_10_match


theorem leaf_147_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T147_49
      hfix147_49 hinj147_49 hcardT147_49
      (fun i => conj_mem_of_fixedPoints _ _ (T147_49 i) (hfix147_49 i) _)
      ⟨147, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T147_49_2 Q2.hfix147_49_2 Q2.hinj147_49_2
      Q2.hcardT147_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_49_2 i) (Q2.hfix147_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T147_49 = colFn colCertDiv_147_49_15.D1 (m := 1) from colCertDiv_147_49_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 15 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T147_49_2 = colFn colCertDiv_147_49_15.D2 (m := 1) from colCertDiv_147_49_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_49_15_match


theorem leaf_147_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T147_49
      hfix147_49 hinj147_49 hcardT147_49
      (fun i => conj_mem_of_fixedPoints _ _ (T147_49 i) (hfix147_49 i) _)
      ⟨147, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T147_49_2 Q2.hfix147_49_2 Q2.hinj147_49_2
      Q2.hcardT147_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_49_2 i) (Q2.hfix147_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T147_49 = colFn colCertDiv_147_49_20.D1 (m := 1) from colCertDiv_147_49_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 20 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T147_49_2 = colFn colCertDiv_147_49_20.D2 (m := 1) from colCertDiv_147_49_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_49_20_match


theorem leaf_147_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T147_50
      hfix147_50 hinj147_50 hcardT147_50
      (fun i => conj_mem_of_fixedPoints _ _ (T147_50 i) (hfix147_50 i) _)
      ⟨147, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T147_50_2 Q2.hfix147_50_2 Q2.hinj147_50_2
      Q2.hcardT147_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_50_2 i) (Q2.hfix147_50_2 i) _)
      colCert_147_50_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T147_50
      hfix147_50 hinj147_50 hcardT147_50
      (fun i => conj_mem_of_fixedPoints _ _ (T147_50 i) (hfix147_50 i) _)
      ⟨147, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T147_50_2 Q2.hfix147_50_2 Q2.hinj147_50_2
      Q2.hcardT147_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_50_2 i) (Q2.hfix147_50_2 i) _)
      colCert_147_50_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T147_50
      hfix147_50 hinj147_50 hcardT147_50
      (fun i => conj_mem_of_fixedPoints _ _ (T147_50 i) (hfix147_50 i) _)
      ⟨147, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T147_50_2 Q2.hfix147_50_2 Q2.hinj147_50_2
      Q2.hcardT147_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_50_2 i) (Q2.hfix147_50_2 i) _)
      colCert_147_50_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T147_50
      hfix147_50 hinj147_50 hcardT147_50
      (fun i => conj_mem_of_fixedPoints _ _ (T147_50 i) (hfix147_50 i) _)
      ⟨147, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T147_50_2 Q2.hfix147_50_2 Q2.hinj147_50_2
      Q2.hcardT147_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_50_2 i) (Q2.hfix147_50_2 i) _)
      colCert_147_50_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T147_50
      hfix147_50 hinj147_50 hcardT147_50
      (fun i => conj_mem_of_fixedPoints _ _ (T147_50 i) (hfix147_50 i) _)
      ⟨147, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T147_50_2 Q2.hfix147_50_2 Q2.hinj147_50_2
      Q2.hcardT147_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_50_2 i) (Q2.hfix147_50_2 i) _)
      colCert_147_50_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T147_50
      hfix147_50 hinj147_50 hcardT147_50
      (fun i => conj_mem_of_fixedPoints _ _ (T147_50 i) (hfix147_50 i) _)
      ⟨147, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T147_50_2 Q2.hfix147_50_2 Q2.hinj147_50_2
      Q2.hcardT147_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_50_2 i) (Q2.hfix147_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T147_50 = colFn colCertDiv_147_50_5.D1 (m := 1) from colCertDiv_147_50_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 5 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T147_50_2 = colFn colCertDiv_147_50_5.D2 (m := 1) from colCertDiv_147_50_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_50_5_match


theorem leaf_147_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T147_50
      hfix147_50 hinj147_50 hcardT147_50
      (fun i => conj_mem_of_fixedPoints _ _ (T147_50 i) (hfix147_50 i) _)
      ⟨147, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T147_50_2 Q2.hfix147_50_2 Q2.hinj147_50_2
      Q2.hcardT147_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_50_2 i) (Q2.hfix147_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T147_50 = colFn colCertDiv_147_50_10.D1 (m := 1) from colCertDiv_147_50_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 10 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T147_50_2 = colFn colCertDiv_147_50_10.D2 (m := 1) from colCertDiv_147_50_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_50_10_match


theorem leaf_147_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T147_50
      hfix147_50 hinj147_50 hcardT147_50
      (fun i => conj_mem_of_fixedPoints _ _ (T147_50 i) (hfix147_50 i) _)
      ⟨147, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T147_50_2 Q2.hfix147_50_2 Q2.hinj147_50_2
      Q2.hcardT147_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_50_2 i) (Q2.hfix147_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T147_50 = colFn colCertDiv_147_50_15.D1 (m := 1) from colCertDiv_147_50_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 15 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T147_50_2 = colFn colCertDiv_147_50_15.D2 (m := 1) from colCertDiv_147_50_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_50_15_match


theorem leaf_147_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T147_50
      hfix147_50 hinj147_50 hcardT147_50
      (fun i => conj_mem_of_fixedPoints _ _ (T147_50 i) (hfix147_50 i) _)
      ⟨147, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T147_50_2 Q2.hfix147_50_2 Q2.hinj147_50_2
      Q2.hcardT147_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_50_2 i) (Q2.hfix147_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T147_50 = colFn colCertDiv_147_50_20.D1 (m := 1) from colCertDiv_147_50_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 20 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T147_50_2 = colFn colCertDiv_147_50_20.D2 (m := 1) from colCertDiv_147_50_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_50_20_match


theorem leaf_147_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T147_51
      hfix147_51 hinj147_51 hcardT147_51
      (fun i => conj_mem_of_fixedPoints _ _ (T147_51 i) (hfix147_51 i) _)
      ⟨147, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T147_51_2 Q2.hfix147_51_2 Q2.hinj147_51_2
      Q2.hcardT147_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_51_2 i) (Q2.hfix147_51_2 i) _)
      colCert_147_51_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T147_51
      hfix147_51 hinj147_51 hcardT147_51
      (fun i => conj_mem_of_fixedPoints _ _ (T147_51 i) (hfix147_51 i) _)
      ⟨147, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T147_51_2 Q2.hfix147_51_2 Q2.hinj147_51_2
      Q2.hcardT147_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_51_2 i) (Q2.hfix147_51_2 i) _)
      colCert_147_51_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T147_51
      hfix147_51 hinj147_51 hcardT147_51
      (fun i => conj_mem_of_fixedPoints _ _ (T147_51 i) (hfix147_51 i) _)
      ⟨147, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T147_51_2 Q2.hfix147_51_2 Q2.hinj147_51_2
      Q2.hcardT147_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_51_2 i) (Q2.hfix147_51_2 i) _)
      colCert_147_51_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T147_51
      hfix147_51 hinj147_51 hcardT147_51
      (fun i => conj_mem_of_fixedPoints _ _ (T147_51 i) (hfix147_51 i) _)
      ⟨147, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T147_51_2 Q2.hfix147_51_2 Q2.hinj147_51_2
      Q2.hcardT147_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_51_2 i) (Q2.hfix147_51_2 i) _)
      colCert_147_51_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T147_51
      hfix147_51 hinj147_51 hcardT147_51
      (fun i => conj_mem_of_fixedPoints _ _ (T147_51 i) (hfix147_51 i) _)
      ⟨147, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T147_51_2 Q2.hfix147_51_2 Q2.hinj147_51_2
      Q2.hcardT147_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_51_2 i) (Q2.hfix147_51_2 i) _)
      colCert_147_51_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T147_51
      hfix147_51 hinj147_51 hcardT147_51
      (fun i => conj_mem_of_fixedPoints _ _ (T147_51 i) (hfix147_51 i) _)
      ⟨147, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T147_51_2 Q2.hfix147_51_2 Q2.hinj147_51_2
      Q2.hcardT147_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_51_2 i) (Q2.hfix147_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T147_51 = colFn colCertDiv_147_51_5.D1 (m := 1) from colCertDiv_147_51_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 5 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T147_51_2 = colFn colCertDiv_147_51_5.D2 (m := 1) from colCertDiv_147_51_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_51_5_match


theorem leaf_147_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T147_51
      hfix147_51 hinj147_51 hcardT147_51
      (fun i => conj_mem_of_fixedPoints _ _ (T147_51 i) (hfix147_51 i) _)
      ⟨147, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T147_51_2 Q2.hfix147_51_2 Q2.hinj147_51_2
      Q2.hcardT147_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_51_2 i) (Q2.hfix147_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T147_51 = colFn colCertDiv_147_51_10.D1 (m := 1) from colCertDiv_147_51_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 10 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T147_51_2 = colFn colCertDiv_147_51_10.D2 (m := 1) from colCertDiv_147_51_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_51_10_match


theorem leaf_147_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T147_51
      hfix147_51 hinj147_51 hcardT147_51
      (fun i => conj_mem_of_fixedPoints _ _ (T147_51 i) (hfix147_51 i) _)
      ⟨147, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T147_51_2 Q2.hfix147_51_2 Q2.hinj147_51_2
      Q2.hcardT147_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_51_2 i) (Q2.hfix147_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T147_51 = colFn colCertDiv_147_51_15.D1 (m := 1) from colCertDiv_147_51_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 15 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T147_51_2 = colFn colCertDiv_147_51_15.D2 (m := 1) from colCertDiv_147_51_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_51_15_match


theorem leaf_147_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T147_51
      hfix147_51 hinj147_51 hcardT147_51
      (fun i => conj_mem_of_fixedPoints _ _ (T147_51 i) (hfix147_51 i) _)
      ⟨147, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T147_51_2 Q2.hfix147_51_2 Q2.hinj147_51_2
      Q2.hcardT147_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_51_2 i) (Q2.hfix147_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T147_51 = colFn colCertDiv_147_51_20.D1 (m := 1) from colCertDiv_147_51_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 20 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T147_51_2 = colFn colCertDiv_147_51_20.D2 (m := 1) from colCertDiv_147_51_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_51_20_match


theorem leaf_147_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T147_52
      hfix147_52 hinj147_52 hcardT147_52
      (fun i => conj_mem_of_fixedPoints _ _ (T147_52 i) (hfix147_52 i) _)
      ⟨147, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T147_52_2 Q2.hfix147_52_2 Q2.hinj147_52_2
      Q2.hcardT147_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_52_2 i) (Q2.hfix147_52_2 i) _)
      colCert_147_52_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T147_52
      hfix147_52 hinj147_52 hcardT147_52
      (fun i => conj_mem_of_fixedPoints _ _ (T147_52 i) (hfix147_52 i) _)
      ⟨147, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T147_52_2 Q2.hfix147_52_2 Q2.hinj147_52_2
      Q2.hcardT147_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_52_2 i) (Q2.hfix147_52_2 i) _)
      colCert_147_52_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T147_52
      hfix147_52 hinj147_52 hcardT147_52
      (fun i => conj_mem_of_fixedPoints _ _ (T147_52 i) (hfix147_52 i) _)
      ⟨147, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T147_52_2 Q2.hfix147_52_2 Q2.hinj147_52_2
      Q2.hcardT147_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_52_2 i) (Q2.hfix147_52_2 i) _)
      colCert_147_52_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T147_52
      hfix147_52 hinj147_52 hcardT147_52
      (fun i => conj_mem_of_fixedPoints _ _ (T147_52 i) (hfix147_52 i) _)
      ⟨147, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T147_52_2 Q2.hfix147_52_2 Q2.hinj147_52_2
      Q2.hcardT147_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_52_2 i) (Q2.hfix147_52_2 i) _)
      colCert_147_52_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T147_52
      hfix147_52 hinj147_52 hcardT147_52
      (fun i => conj_mem_of_fixedPoints _ _ (T147_52 i) (hfix147_52 i) _)
      ⟨147, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T147_52_2 Q2.hfix147_52_2 Q2.hinj147_52_2
      Q2.hcardT147_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_52_2 i) (Q2.hfix147_52_2 i) _)
      colCert_147_52_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T147_52
      hfix147_52 hinj147_52 hcardT147_52
      (fun i => conj_mem_of_fixedPoints _ _ (T147_52 i) (hfix147_52 i) _)
      ⟨147, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T147_52_2 Q2.hfix147_52_2 Q2.hinj147_52_2
      Q2.hcardT147_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_52_2 i) (Q2.hfix147_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T147_52 = colFn colCertDiv_147_52_5.D1 (m := 1) from colCertDiv_147_52_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T147_52_2 = colFn colCertDiv_147_52_5.D2 (m := 1) from colCertDiv_147_52_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_52_5_match


theorem leaf_147_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T147_52
      hfix147_52 hinj147_52 hcardT147_52
      (fun i => conj_mem_of_fixedPoints _ _ (T147_52 i) (hfix147_52 i) _)
      ⟨147, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T147_52_2 Q2.hfix147_52_2 Q2.hinj147_52_2
      Q2.hcardT147_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_52_2 i) (Q2.hfix147_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T147_52 = colFn colCertDiv_147_52_10.D1 (m := 1) from colCertDiv_147_52_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T147_52_2 = colFn colCertDiv_147_52_10.D2 (m := 1) from colCertDiv_147_52_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_52_10_match


theorem leaf_147_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T147_52
      hfix147_52 hinj147_52 hcardT147_52
      (fun i => conj_mem_of_fixedPoints _ _ (T147_52 i) (hfix147_52 i) _)
      ⟨147, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T147_52_2 Q2.hfix147_52_2 Q2.hinj147_52_2
      Q2.hcardT147_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_52_2 i) (Q2.hfix147_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T147_52 = colFn colCertDiv_147_52_15.D1 (m := 1) from colCertDiv_147_52_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T147_52_2 = colFn colCertDiv_147_52_15.D2 (m := 1) from colCertDiv_147_52_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_52_15_match


theorem leaf_147_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T147_52
      hfix147_52 hinj147_52 hcardT147_52
      (fun i => conj_mem_of_fixedPoints _ _ (T147_52 i) (hfix147_52 i) _)
      ⟨147, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T147_52_2 Q2.hfix147_52_2 Q2.hinj147_52_2
      Q2.hcardT147_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_52_2 i) (Q2.hfix147_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T147_52 = colFn colCertDiv_147_52_20.D1 (m := 1) from colCertDiv_147_52_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T147_52_2 = colFn colCertDiv_147_52_20.D2 (m := 1) from colCertDiv_147_52_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_52_20_match


theorem leaf_147_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T147_53
      hfix147_53 hinj147_53 hcardT147_53
      (fun i => conj_mem_of_fixedPoints _ _ (T147_53 i) (hfix147_53 i) _)
      ⟨147, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T147_53_2 Q2.hfix147_53_2 Q2.hinj147_53_2
      Q2.hcardT147_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_53_2 i) (Q2.hfix147_53_2 i) _)
      colCert_147_53_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T147_53
      hfix147_53 hinj147_53 hcardT147_53
      (fun i => conj_mem_of_fixedPoints _ _ (T147_53 i) (hfix147_53 i) _)
      ⟨147, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T147_53_2 Q2.hfix147_53_2 Q2.hinj147_53_2
      Q2.hcardT147_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_53_2 i) (Q2.hfix147_53_2 i) _)
      colCert_147_53_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T147_53
      hfix147_53 hinj147_53 hcardT147_53
      (fun i => conj_mem_of_fixedPoints _ _ (T147_53 i) (hfix147_53 i) _)
      ⟨147, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T147_53_2 Q2.hfix147_53_2 Q2.hinj147_53_2
      Q2.hcardT147_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_53_2 i) (Q2.hfix147_53_2 i) _)
      colCert_147_53_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T147_53
      hfix147_53 hinj147_53 hcardT147_53
      (fun i => conj_mem_of_fixedPoints _ _ (T147_53 i) (hfix147_53 i) _)
      ⟨147, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T147_53_2 Q2.hfix147_53_2 Q2.hinj147_53_2
      Q2.hcardT147_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_53_2 i) (Q2.hfix147_53_2 i) _)
      colCert_147_53_3.hD ?_).symm
  rw [alnId_147 j hj]


end LeanDring.P5Presentation
