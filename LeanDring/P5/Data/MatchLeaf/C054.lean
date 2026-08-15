/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C031
import LeanDring.P5.Data.ColRestCheap.C121
import LeanDring.P5.Data.ColRestCheap.C122
import LeanDring.P5.Data.ColRestCheap.C123
import LeanDring.P5.Data.ColRestCheap.C124
import LeanDring.P5.Data.ColTau.C003
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C041
import LeanDring.P5.Data.SpeciesDiv.C042
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk03

/-! # Stage-5 leaves, chunk 53 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_147_81_2 (hp : 2 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp)) T147_81
      hfix147_81 hinj147_81 hcardT147_81
      (fun i => conj_mem_of_fixedPoints _ _ (T147_81 i) (hfix147_81 i) _)
      ⟨147, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 2 hp) Q2.T147_81_2 Q2.hfix147_81_2 Q2.hinj147_81_2
      Q2.hcardT147_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_81_2 i) (Q2.hfix147_81_2 i) _)
      colCert_147_81_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_81_3 (hp : 3 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp)) T147_81
      hfix147_81 hinj147_81 hcardT147_81
      (fun i => conj_mem_of_fixedPoints _ _ (T147_81 i) (hfix147_81 i) _)
      ⟨147, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 3 hp) Q2.T147_81_2 Q2.hfix147_81_2 Q2.hinj147_81_2
      Q2.hcardT147_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_81_2 i) (Q2.hfix147_81_2 i) _)
      colCert_147_81_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_81_4 (hp : 4 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp)) T147_81
      hfix147_81 hinj147_81 hcardT147_81
      (fun i => conj_mem_of_fixedPoints _ _ (T147_81 i) (hfix147_81 i) _)
      ⟨147, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 4 hp) Q2.T147_81_2 Q2.hfix147_81_2 Q2.hinj147_81_2
      Q2.hcardT147_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_81_2 i) (Q2.hfix147_81_2 i) _)
      colCert_147_81_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_81_5 (hp : 5 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp)) T147_81
      hfix147_81 hinj147_81 hcardT147_81
      (fun i => conj_mem_of_fixedPoints _ _ (T147_81 i) (hfix147_81 i) _)
      ⟨147, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 5 hp) Q2.T147_81_2 Q2.hfix147_81_2 Q2.hinj147_81_2
      Q2.hcardT147_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_81_2 i) (Q2.hfix147_81_2 i) _)
      colCert_147_81_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_81_10 (hp : 10 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp)) T147_81
      hfix147_81 hinj147_81 hcardT147_81
      (fun i => conj_mem_of_fixedPoints _ _ (T147_81 i) (hfix147_81 i) _)
      ⟨147, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 10 hp) Q2.T147_81_2 Q2.hfix147_81_2 Q2.hinj147_81_2
      Q2.hcardT147_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_81_2 i) (Q2.hfix147_81_2 i) _)
      colCert_147_81_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_81_15 (hp : 15 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp)) T147_81
      hfix147_81 hinj147_81 hcardT147_81
      (fun i => conj_mem_of_fixedPoints _ _ (T147_81 i) (hfix147_81 i) _)
      ⟨147, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 15 hp) Q2.T147_81_2 Q2.hfix147_81_2 Q2.hinj147_81_2
      Q2.hcardT147_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_81_2 i) (Q2.hfix147_81_2 i) _)
      colCert_147_81_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_81_20 (hp : 20 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp)) T147_81
      hfix147_81 hinj147_81 hcardT147_81
      (fun i => conj_mem_of_fixedPoints _ _ (T147_81 i) (hfix147_81 i) _)
      ⟨147, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 20 hp) Q2.T147_81_2 Q2.hfix147_81_2 Q2.hinj147_81_2
      Q2.hcardT147_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_81_2 i) (Q2.hfix147_81_2 i) _)
      colCert_147_81_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_82_0 (hp : 0 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp)) T147_82
      hfix147_82 hinj147_82 hcardT147_82
      (fun i => conj_mem_of_fixedPoints _ _ (T147_82 i) (hfix147_82 i) _)
      ⟨147, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 0 hp) Q2.T147_82_2 Q2.hfix147_82_2 Q2.hinj147_82_2
      Q2.hcardT147_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_82_2 i) (Q2.hfix147_82_2 i) _)
      colCert_147_82_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_82_1 (hp : 1 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp)) T147_82
      hfix147_82 hinj147_82 hcardT147_82
      (fun i => conj_mem_of_fixedPoints _ _ (T147_82 i) (hfix147_82 i) _)
      ⟨147, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 1 hp) Q2.T147_82_2 Q2.hfix147_82_2 Q2.hinj147_82_2
      Q2.hcardT147_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_82_2 i) (Q2.hfix147_82_2 i) _)
      colCert_147_82_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_82_2 (hp : 2 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp)) T147_82
      hfix147_82 hinj147_82 hcardT147_82
      (fun i => conj_mem_of_fixedPoints _ _ (T147_82 i) (hfix147_82 i) _)
      ⟨147, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 2 hp) Q2.T147_82_2 Q2.hfix147_82_2 Q2.hinj147_82_2
      Q2.hcardT147_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_82_2 i) (Q2.hfix147_82_2 i) _)
      colCert_147_82_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_82_3 (hp : 3 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp)) T147_82
      hfix147_82 hinj147_82 hcardT147_82
      (fun i => conj_mem_of_fixedPoints _ _ (T147_82 i) (hfix147_82 i) _)
      ⟨147, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 3 hp) Q2.T147_82_2 Q2.hfix147_82_2 Q2.hinj147_82_2
      Q2.hcardT147_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_82_2 i) (Q2.hfix147_82_2 i) _)
      colCert_147_82_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_82_4 (hp : 4 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp)) T147_82
      hfix147_82 hinj147_82 hcardT147_82
      (fun i => conj_mem_of_fixedPoints _ _ (T147_82 i) (hfix147_82 i) _)
      ⟨147, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 4 hp) Q2.T147_82_2 Q2.hfix147_82_2 Q2.hinj147_82_2
      Q2.hcardT147_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_82_2 i) (Q2.hfix147_82_2 i) _)
      colCert_147_82_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_82_5 (hp : 5 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp)) T147_82
      hfix147_82 hinj147_82 hcardT147_82
      (fun i => conj_mem_of_fixedPoints _ _ (T147_82 i) (hfix147_82 i) _)
      ⟨147, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 5 hp) Q2.T147_82_2 Q2.hfix147_82_2 Q2.hinj147_82_2
      Q2.hcardT147_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_82_2 i) (Q2.hfix147_82_2 i) _)
      colCert_147_82_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_82_10 (hp : 10 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp)) T147_82
      hfix147_82 hinj147_82 hcardT147_82
      (fun i => conj_mem_of_fixedPoints _ _ (T147_82 i) (hfix147_82 i) _)
      ⟨147, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 10 hp) Q2.T147_82_2 Q2.hfix147_82_2 Q2.hinj147_82_2
      Q2.hcardT147_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_82_2 i) (Q2.hfix147_82_2 i) _)
      colCert_147_82_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_82_15 (hp : 15 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp)) T147_82
      hfix147_82 hinj147_82 hcardT147_82
      (fun i => conj_mem_of_fixedPoints _ _ (T147_82 i) (hfix147_82 i) _)
      ⟨147, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 15 hp) Q2.T147_82_2 Q2.hfix147_82_2 Q2.hinj147_82_2
      Q2.hcardT147_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_82_2 i) (Q2.hfix147_82_2 i) _)
      colCert_147_82_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_82_20 (hp : 20 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp)) T147_82
      hfix147_82 hinj147_82 hcardT147_82
      (fun i => conj_mem_of_fixedPoints _ _ (T147_82 i) (hfix147_82 i) _)
      ⟨147, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 20 hp) Q2.T147_82_2 Q2.hfix147_82_2 Q2.hinj147_82_2
      Q2.hcardT147_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_82_2 i) (Q2.hfix147_82_2 i) _)
      colCert_147_82_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_83_0 (hp : 0 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp)) T147_83
      hfix147_83 hinj147_83 hcardT147_83
      (fun i => conj_mem_of_fixedPoints _ _ (T147_83 i) (hfix147_83 i) _)
      ⟨147, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 0 hp) Q2.T147_83_2 Q2.hfix147_83_2 Q2.hinj147_83_2
      Q2.hcardT147_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_83_2 i) (Q2.hfix147_83_2 i) _)
      colCert_147_83_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_83_1 (hp : 1 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp)) T147_83
      hfix147_83 hinj147_83 hcardT147_83
      (fun i => conj_mem_of_fixedPoints _ _ (T147_83 i) (hfix147_83 i) _)
      ⟨147, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 1 hp) Q2.T147_83_2 Q2.hfix147_83_2 Q2.hinj147_83_2
      Q2.hcardT147_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_83_2 i) (Q2.hfix147_83_2 i) _)
      colCert_147_83_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_83_2 (hp : 2 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp)) T147_83
      hfix147_83 hinj147_83 hcardT147_83
      (fun i => conj_mem_of_fixedPoints _ _ (T147_83 i) (hfix147_83 i) _)
      ⟨147, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 2 hp) Q2.T147_83_2 Q2.hfix147_83_2 Q2.hinj147_83_2
      Q2.hcardT147_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_83_2 i) (Q2.hfix147_83_2 i) _)
      colCert_147_83_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_83_3 (hp : 3 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp)) T147_83
      hfix147_83 hinj147_83 hcardT147_83
      (fun i => conj_mem_of_fixedPoints _ _ (T147_83 i) (hfix147_83 i) _)
      ⟨147, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 3 hp) Q2.T147_83_2 Q2.hfix147_83_2 Q2.hinj147_83_2
      Q2.hcardT147_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_83_2 i) (Q2.hfix147_83_2 i) _)
      colCert_147_83_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_83_4 (hp : 4 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp)) T147_83
      hfix147_83 hinj147_83 hcardT147_83
      (fun i => conj_mem_of_fixedPoints _ _ (T147_83 i) (hfix147_83 i) _)
      ⟨147, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 4 hp) Q2.T147_83_2 Q2.hfix147_83_2 Q2.hinj147_83_2
      Q2.hcardT147_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_83_2 i) (Q2.hfix147_83_2 i) _)
      colCert_147_83_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_83_5 (hp : 5 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp)) T147_83
      hfix147_83 hinj147_83 hcardT147_83
      (fun i => conj_mem_of_fixedPoints _ _ (T147_83 i) (hfix147_83 i) _)
      ⟨147, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 5 hp) Q2.T147_83_2 Q2.hfix147_83_2 Q2.hinj147_83_2
      Q2.hcardT147_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_83_2 i) (Q2.hfix147_83_2 i) _)
      colCert_147_83_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_83_10 (hp : 10 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp)) T147_83
      hfix147_83 hinj147_83 hcardT147_83
      (fun i => conj_mem_of_fixedPoints _ _ (T147_83 i) (hfix147_83 i) _)
      ⟨147, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 10 hp) Q2.T147_83_2 Q2.hfix147_83_2 Q2.hinj147_83_2
      Q2.hcardT147_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_83_2 i) (Q2.hfix147_83_2 i) _)
      colCert_147_83_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_83_15 (hp : 15 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp)) T147_83
      hfix147_83 hinj147_83 hcardT147_83
      (fun i => conj_mem_of_fixedPoints _ _ (T147_83 i) (hfix147_83 i) _)
      ⟨147, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 15 hp) Q2.T147_83_2 Q2.hfix147_83_2 Q2.hinj147_83_2
      Q2.hcardT147_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_83_2 i) (Q2.hfix147_83_2 i) _)
      colCert_147_83_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_83_20 (hp : 20 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp)) T147_83
      hfix147_83 hinj147_83 hcardT147_83
      (fun i => conj_mem_of_fixedPoints _ _ (T147_83 i) (hfix147_83 i) _)
      ⟨147, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 20 hp) Q2.T147_83_2 Q2.hfix147_83_2 Q2.hinj147_83_2
      Q2.hcardT147_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_83_2 i) (Q2.hfix147_83_2 i) _)
      colCert_147_83_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_84_0 (hp : 0 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp)) T147_84
      hfix147_84 hinj147_84 hcardT147_84
      (fun i => conj_mem_of_fixedPoints _ _ (T147_84 i) (hfix147_84 i) _)
      ⟨147, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 0 hp) Q2.T147_84_2 Q2.hfix147_84_2 Q2.hinj147_84_2
      Q2.hcardT147_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_84_2 i) (Q2.hfix147_84_2 i) _)
      colCert_147_84_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_84_1 (hp : 1 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp)) T147_84
      hfix147_84 hinj147_84 hcardT147_84
      (fun i => conj_mem_of_fixedPoints _ _ (T147_84 i) (hfix147_84 i) _)
      ⟨147, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 1 hp) Q2.T147_84_2 Q2.hfix147_84_2 Q2.hinj147_84_2
      Q2.hcardT147_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_84_2 i) (Q2.hfix147_84_2 i) _)
      colCert_147_84_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_84_2 (hp : 2 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp)) T147_84
      hfix147_84 hinj147_84 hcardT147_84
      (fun i => conj_mem_of_fixedPoints _ _ (T147_84 i) (hfix147_84 i) _)
      ⟨147, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 2 hp) Q2.T147_84_2 Q2.hfix147_84_2 Q2.hinj147_84_2
      Q2.hcardT147_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_84_2 i) (Q2.hfix147_84_2 i) _)
      colCert_147_84_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_84_3 (hp : 3 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp)) T147_84
      hfix147_84 hinj147_84 hcardT147_84
      (fun i => conj_mem_of_fixedPoints _ _ (T147_84 i) (hfix147_84 i) _)
      ⟨147, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 3 hp) Q2.T147_84_2 Q2.hfix147_84_2 Q2.hinj147_84_2
      Q2.hcardT147_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_84_2 i) (Q2.hfix147_84_2 i) _)
      colCert_147_84_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_84_4 (hp : 4 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp)) T147_84
      hfix147_84 hinj147_84 hcardT147_84
      (fun i => conj_mem_of_fixedPoints _ _ (T147_84 i) (hfix147_84 i) _)
      ⟨147, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 4 hp) Q2.T147_84_2 Q2.hfix147_84_2 Q2.hinj147_84_2
      Q2.hcardT147_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_84_2 i) (Q2.hfix147_84_2 i) _)
      colCert_147_84_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_84_5 (hp : 5 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp)) T147_84
      hfix147_84 hinj147_84 hcardT147_84
      (fun i => conj_mem_of_fixedPoints _ _ (T147_84 i) (hfix147_84 i) _)
      ⟨147, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 5 hp) Q2.T147_84_2 Q2.hfix147_84_2 Q2.hinj147_84_2
      Q2.hcardT147_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_84_2 i) (Q2.hfix147_84_2 i) _)
      colCert_147_84_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_84_10 (hp : 10 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp)) T147_84
      hfix147_84 hinj147_84 hcardT147_84
      (fun i => conj_mem_of_fixedPoints _ _ (T147_84 i) (hfix147_84 i) _)
      ⟨147, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 10 hp) Q2.T147_84_2 Q2.hfix147_84_2 Q2.hinj147_84_2
      Q2.hcardT147_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_84_2 i) (Q2.hfix147_84_2 i) _)
      colCert_147_84_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_84_15 (hp : 15 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp)) T147_84
      hfix147_84 hinj147_84 hcardT147_84
      (fun i => conj_mem_of_fixedPoints _ _ (T147_84 i) (hfix147_84 i) _)
      ⟨147, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 15 hp) Q2.T147_84_2 Q2.hfix147_84_2 Q2.hinj147_84_2
      Q2.hcardT147_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_84_2 i) (Q2.hfix147_84_2 i) _)
      colCert_147_84_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_84_20 (hp : 20 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp)) T147_84
      hfix147_84 hinj147_84 hcardT147_84
      (fun i => conj_mem_of_fixedPoints _ _ (T147_84 i) (hfix147_84 i) _)
      ⟨147, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 20 hp) Q2.T147_84_2 Q2.hfix147_84_2 Q2.hinj147_84_2
      Q2.hcardT147_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_84_2 i) (Q2.hfix147_84_2 i) _)
      colCert_147_84_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_0 (hp : 0 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 0 (transLenTr ⟨85, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 0 (transLenTr ⟨85, by decide⟩ 0 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 0 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_1 (hp : 1 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 1 (transLenTr ⟨85, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 1 (transLenTr ⟨85, by decide⟩ 1 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 1 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_2 (hp : 2 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 2 (transLenTr ⟨85, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 2 (transLenTr ⟨85, by decide⟩ 2 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 2 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_3 (hp : 3 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 3 (transLenTr ⟨85, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 3 (transLenTr ⟨85, by decide⟩ 3 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 3 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_4 (hp : 4 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 4 (transLenTr ⟨85, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 4 (transLenTr ⟨85, by decide⟩ 4 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 4 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_5 (hp : 5 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 5 (transLenTr ⟨85, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 5 (transLenTr ⟨85, by decide⟩ 5 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 5 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_6 (hp : 6 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 6 (transLenTr ⟨85, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 6 (transLenTr ⟨85, by decide⟩ 6 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 6 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_7 (hp : 7 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 7 (transLenTr ⟨85, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 7 (transLenTr ⟨85, by decide⟩ 7 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 7 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_8 (hp : 8 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 8 (transLenTr ⟨85, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 8 (transLenTr ⟨85, by decide⟩ 8 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 8 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_9 (hp : 9 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 9 (transLenTr ⟨85, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 9 (transLenTr ⟨85, by decide⟩ 9 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 9 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_10 (hp : 10 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 10 (transLenTr ⟨85, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 10 (transLenTr ⟨85, by decide⟩ 10 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 10 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_11 (hp : 11 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 11 (transLenTr ⟨85, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 11 (transLenTr ⟨85, by decide⟩ 11 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 11 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_12 (hp : 12 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 12 (transLenTr ⟨85, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 12 (transLenTr ⟨85, by decide⟩ 12 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 12 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_13 (hp : 13 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 13 (transLenTr ⟨85, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 13 (transLenTr ⟨85, by decide⟩ 13 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 13 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_14 (hp : 14 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 14 (transLenTr ⟨85, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 14 (transLenTr ⟨85, by decide⟩ 14 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 14 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_15 (hp : 15 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 15 (transLenTr ⟨85, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 15 (transLenTr ⟨85, by decide⟩ 15 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 15 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_16 (hp : 16 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 16 (transLenTr ⟨85, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 16 (transLenTr ⟨85, by decide⟩ 16 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 16 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_17 (hp : 17 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 17 (transLenTr ⟨85, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 17 (transLenTr ⟨85, by decide⟩ 17 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 17 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_18 (hp : 18 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 18 (transLenTr ⟨85, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 18 (transLenTr ⟨85, by decide⟩ 18 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 18 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_19 (hp : 19 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 19 (transLenTr ⟨85, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 19 (transLenTr ⟨85, by decide⟩ 19 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 19 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_20 (hp : 20 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 20 (transLenTr ⟨85, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 20 (transLenTr ⟨85, by decide⟩ 20 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 20 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_21 (hp : 21 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 21 (transLenTr ⟨85, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 21 (transLenTr ⟨85, by decide⟩ 21 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 21 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_22 (hp : 22 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 22 (transLenTr ⟨85, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 22 (transLenTr ⟨85, by decide⟩ 22 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 22 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_23 (hp : 23 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 23 (transLenTr ⟨85, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 23 (transLenTr ⟨85, by decide⟩ 23 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 23 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_24 (hp : 24 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 24 (transLenTr ⟨85, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 24 (transLenTr ⟨85, by decide⟩ 24 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 24 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_25 (hp : 25 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 25 (transLenTr ⟨85, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 25 (transLenTr ⟨85, by decide⟩ 25 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 25 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_30 (hp : 30 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 30 (transLenTr ⟨85, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 30 (transLenTr ⟨85, by decide⟩ 30 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 30 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_35 (hp : 35 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 35 (transLenTr ⟨85, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 35 (transLenTr ⟨85, by decide⟩ 35 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 35 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_40 (hp : 40 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 40 (transLenTr ⟨85, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 40 (transLenTr ⟨85, by decide⟩ 40 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 40 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_45 (hp : 45 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 45 (transLenTr ⟨85, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 45 (transLenTr ⟨85, by decide⟩ 45 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 45 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      colCert_147_85_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_85_50 (hp : 50 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 50 (transLenTr ⟨85, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 50 (transLenTr ⟨85, by decide⟩ 50 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 50 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 50 (transLenTr ⟨85, by decide⟩ 50 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_50.D1 (m := 1) from colCertDiv_147_85_50.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 50 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_50.D2 (m := 1) from colCertDiv_147_85_50.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_50_tau_match


theorem leaf_147_85_55 (hp : 55 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 55 (transLenTr ⟨85, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 55 (transLenTr ⟨85, by decide⟩ 55 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 55 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 55 (transLenTr ⟨85, by decide⟩ 55 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_55.D1 (m := 1) from colCertDiv_147_85_55.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 55 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_55.D2 (m := 1) from colCertDiv_147_85_55.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_55_tau_match


theorem leaf_147_85_60 (hp : 60 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 60 (transLenTr ⟨85, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 60 (transLenTr ⟨85, by decide⟩ 60 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 60 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 60 (transLenTr ⟨85, by decide⟩ 60 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_60.D1 (m := 1) from colCertDiv_147_85_60.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 60 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_60.D2 (m := 1) from colCertDiv_147_85_60.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_60_tau_match


theorem leaf_147_85_65 (hp : 65 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 65 (transLenTr ⟨85, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 65 (transLenTr ⟨85, by decide⟩ 65 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 65 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 65 (transLenTr ⟨85, by decide⟩ 65 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_65.D1 (m := 1) from colCertDiv_147_85_65.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 65 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_65.D2 (m := 1) from colCertDiv_147_85_65.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_65_tau_match


theorem leaf_147_85_70 (hp : 70 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 70 (transLenTr ⟨85, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 70 (transLenTr ⟨85, by decide⟩ 70 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 70 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 70 (transLenTr ⟨85, by decide⟩ 70 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_70.D1 (m := 1) from colCertDiv_147_85_70.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 70 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_70.D2 (m := 1) from colCertDiv_147_85_70.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_70_tau_match


theorem leaf_147_85_75 (hp : 75 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 75 (transLenTr ⟨85, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 75 (transLenTr ⟨85, by decide⟩ 75 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 75 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 75 (transLenTr ⟨85, by decide⟩ 75 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_75.D1 (m := 1) from colCertDiv_147_85_75.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 75 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_75.D2 (m := 1) from colCertDiv_147_85_75.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_75_tau_match


theorem leaf_147_85_80 (hp : 80 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 80 (transLenTr ⟨85, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 80 (transLenTr ⟨85, by decide⟩ 80 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 80 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 80 (transLenTr ⟨85, by decide⟩ 80 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_80.D1 (m := 1) from colCertDiv_147_85_80.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 80 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_80.D2 (m := 1) from colCertDiv_147_85_80.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_80_tau_match


theorem leaf_147_85_85 (hp : 85 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 85 (transLenTr ⟨85, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 85 (transLenTr ⟨85, by decide⟩ 85 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 85 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 85 (transLenTr ⟨85, by decide⟩ 85 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_85.D1 (m := 1) from colCertDiv_147_85_85.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 85 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_85.D2 (m := 1) from colCertDiv_147_85_85.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_85_tau_match


theorem leaf_147_85_90 (hp : 90 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 90 (transLenTr ⟨85, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 90 (transLenTr ⟨85, by decide⟩ 90 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 90 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 90 (transLenTr ⟨85, by decide⟩ 90 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_90.D1 (m := 1) from colCertDiv_147_85_90.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 90 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_90.D2 (m := 1) from colCertDiv_147_85_90.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_90_tau_match


theorem leaf_147_85_95 (hp : 95 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 95 (transLenTr ⟨85, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 95 (transLenTr ⟨85, by decide⟩ 95 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 95 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 95 (transLenTr ⟨85, by decide⟩ 95 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_95.D1 (m := 1) from colCertDiv_147_85_95.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 95 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_95.D2 (m := 1) from colCertDiv_147_85_95.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_95_tau_match


theorem leaf_147_85_100 (hp : 100 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 100 (transLenTr ⟨85, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 100 (transLenTr ⟨85, by decide⟩ 100 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 100 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 100 (transLenTr ⟨85, by decide⟩ 100 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_100.D1 (m := 1) from colCertDiv_147_85_100.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 100 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_100.D2 (m := 1) from colCertDiv_147_85_100.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_100_tau_match


theorem leaf_147_85_105 (hp : 105 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 105 (transLenTr ⟨85, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 105 (transLenTr ⟨85, by decide⟩ 105 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 105 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 105 (transLenTr ⟨85, by decide⟩ 105 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_105.D1 (m := 1) from colCertDiv_147_85_105.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 105 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_105.D2 (m := 1) from colCertDiv_147_85_105.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_105_tau_match


theorem leaf_147_85_110 (hp : 110 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 110 (transLenTr ⟨85, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 110 (transLenTr ⟨85, by decide⟩ 110 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 110 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 110 (transLenTr ⟨85, by decide⟩ 110 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_110.D1 (m := 1) from colCertDiv_147_85_110.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 110 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_110.D2 (m := 1) from colCertDiv_147_85_110.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_110_tau_match


theorem leaf_147_85_115 (hp : 115 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 115 (transLenTr ⟨85, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 115 (transLenTr ⟨85, by decide⟩ 115 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 115 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 115 (transLenTr ⟨85, by decide⟩ 115 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_115.D1 (m := 1) from colCertDiv_147_85_115.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 115 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_115.D2 (m := 1) from colCertDiv_147_85_115.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_115_tau_match


theorem leaf_147_85_120 (hp : 120 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 120 (transLenTr ⟨85, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 120 (transLenTr ⟨85, by decide⟩ 120 hp)) T147_85
      hfix147_85 hinj147_85 hcardT147_85
      (fun i => conj_mem_of_fixedPoints _ _ (T147_85 i) (hfix147_85 i) _)
      ⟨147, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 120 hp) Q2.T147_85_2 Q2.hfix147_85_2 Q2.hinj147_85_2
      Q2.hcardT147_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_85_2 i) (Q2.hfix147_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 120 (transLenTr ⟨85, by decide⟩ 120 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T147_85 = colFn colCertDiv_147_85_120.D1 (m := 1) from colCertDiv_147_85_120.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 120 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T147_85_2 = colFn colCertDiv_147_85_120.D2 (m := 1) from colCertDiv_147_85_120.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_85_120_tau_match


theorem leaf_147_86_0 (hp : 0 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 0 (transLenTr ⟨86, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 0 (transLenTr ⟨86, by decide⟩ 0 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 0 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 0 (transLenTr ⟨86, by decide⟩ 0 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T147_86 = colFn colCertDiv_147_86_0.D1 (m := 1) from colCertDiv_147_86_0.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 0 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T147_86_2 = colFn colCertDiv_147_86_0.D2 (m := 1) from colCertDiv_147_86_0.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_86_0_tau_match


theorem leaf_147_86_1 (hp : 1 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 1 (transLenTr ⟨86, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 1 (transLenTr ⟨86, by decide⟩ 1 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 1 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 1 (transLenTr ⟨86, by decide⟩ 1 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T147_86 = colFn colCertDiv_147_86_1.D1 (m := 1) from colCertDiv_147_86_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 1 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T147_86_2 = colFn colCertDiv_147_86_1.D2 (m := 1) from colCertDiv_147_86_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_86_1_tau_match


theorem leaf_147_86_2 (hp : 2 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 2 (transLenTr ⟨86, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 2 (transLenTr ⟨86, by decide⟩ 2 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 2 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 2 (transLenTr ⟨86, by decide⟩ 2 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T147_86 = colFn colCertDiv_147_86_2.D1 (m := 1) from colCertDiv_147_86_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 2 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T147_86_2 = colFn colCertDiv_147_86_2.D2 (m := 1) from colCertDiv_147_86_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_86_2_tau_match


theorem leaf_147_86_3 (hp : 3 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 3 (transLenTr ⟨86, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 3 (transLenTr ⟨86, by decide⟩ 3 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 3 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 3 (transLenTr ⟨86, by decide⟩ 3 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T147_86 = colFn colCertDiv_147_86_3.D1 (m := 1) from colCertDiv_147_86_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 3 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T147_86_2 = colFn colCertDiv_147_86_3.D2 (m := 1) from colCertDiv_147_86_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_86_3_tau_match


theorem leaf_147_86_4 (hp : 4 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 4 (transLenTr ⟨86, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 4 (transLenTr ⟨86, by decide⟩ 4 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 4 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 4 (transLenTr ⟨86, by decide⟩ 4 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T147_86 = colFn colCertDiv_147_86_4.D1 (m := 1) from colCertDiv_147_86_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 4 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T147_86_2 = colFn colCertDiv_147_86_4.D2 (m := 1) from colCertDiv_147_86_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_86_4_tau_match


theorem leaf_147_86_5 (hp : 5 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 5 (transLenTr ⟨86, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 5 (transLenTr ⟨86, by decide⟩ 5 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 5 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_6 (hp : 6 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 6 (transLenTr ⟨86, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 6 (transLenTr ⟨86, by decide⟩ 6 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 6 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_7 (hp : 7 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 7 (transLenTr ⟨86, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 7 (transLenTr ⟨86, by decide⟩ 7 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 7 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_8 (hp : 8 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 8 (transLenTr ⟨86, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 8 (transLenTr ⟨86, by decide⟩ 8 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 8 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_9 (hp : 9 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 9 (transLenTr ⟨86, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 9 (transLenTr ⟨86, by decide⟩ 9 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 9 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_10 (hp : 10 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 10 (transLenTr ⟨86, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 10 (transLenTr ⟨86, by decide⟩ 10 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 10 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_11 (hp : 11 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 11 (transLenTr ⟨86, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 11 (transLenTr ⟨86, by decide⟩ 11 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 11 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_12 (hp : 12 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 12 (transLenTr ⟨86, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 12 (transLenTr ⟨86, by decide⟩ 12 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 12 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_13 (hp : 13 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 13 (transLenTr ⟨86, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 13 (transLenTr ⟨86, by decide⟩ 13 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 13 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_14 (hp : 14 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 14 (transLenTr ⟨86, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 14 (transLenTr ⟨86, by decide⟩ 14 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 14 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_15 (hp : 15 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 15 (transLenTr ⟨86, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 15 (transLenTr ⟨86, by decide⟩ 15 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 15 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_16 (hp : 16 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 16 (transLenTr ⟨86, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 16 (transLenTr ⟨86, by decide⟩ 16 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 16 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_17 (hp : 17 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 17 (transLenTr ⟨86, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 17 (transLenTr ⟨86, by decide⟩ 17 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 17 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_18 (hp : 18 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 18 (transLenTr ⟨86, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 18 (transLenTr ⟨86, by decide⟩ 18 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 18 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_19 (hp : 19 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 19 (transLenTr ⟨86, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 19 (transLenTr ⟨86, by decide⟩ 19 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 19 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_20 (hp : 20 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 20 (transLenTr ⟨86, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 20 (transLenTr ⟨86, by decide⟩ 20 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 20 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_21 (hp : 21 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 21 (transLenTr ⟨86, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 21 (transLenTr ⟨86, by decide⟩ 21 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 21 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_22 (hp : 22 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 22 (transLenTr ⟨86, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 22 (transLenTr ⟨86, by decide⟩ 22 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 22 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_23 (hp : 23 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 23 (transLenTr ⟨86, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 23 (transLenTr ⟨86, by decide⟩ 23 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 23 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_86_24 (hp : 24 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 24 (transLenTr ⟨86, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 24 (transLenTr ⟨86, by decide⟩ 24 hp)) T147_86
      hfix147_86 hinj147_86 hcardT147_86
      (fun i => conj_mem_of_fixedPoints _ _ (T147_86 i) (hfix147_86 i) _)
      ⟨147, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 24 hp) Q2.T147_86_2 Q2.hfix147_86_2 Q2.hinj147_86_2
      Q2.hcardT147_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_86_2 i) (Q2.hfix147_86_2 i) _)
      colCert_147_86_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_0 (hp : 0 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 0 (transLenTr ⟨87, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 0 (transLenTr ⟨87, by decide⟩ 0 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 0 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_1 (hp : 1 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 1 (transLenTr ⟨87, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 1 (transLenTr ⟨87, by decide⟩ 1 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 1 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_2 (hp : 2 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 2 (transLenTr ⟨87, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 2 (transLenTr ⟨87, by decide⟩ 2 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 2 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_3 (hp : 3 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 3 (transLenTr ⟨87, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 3 (transLenTr ⟨87, by decide⟩ 3 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 3 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_4 (hp : 4 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 4 (transLenTr ⟨87, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 4 (transLenTr ⟨87, by decide⟩ 4 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 4 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_5 (hp : 5 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 5 (transLenTr ⟨87, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 5 (transLenTr ⟨87, by decide⟩ 5 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 5 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_6 (hp : 6 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 6 (transLenTr ⟨87, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 6 (transLenTr ⟨87, by decide⟩ 6 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 6 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_7 (hp : 7 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 7 (transLenTr ⟨87, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 7 (transLenTr ⟨87, by decide⟩ 7 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 7 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_8 (hp : 8 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 8 (transLenTr ⟨87, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 8 (transLenTr ⟨87, by decide⟩ 8 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 8 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_9 (hp : 9 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 9 (transLenTr ⟨87, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 9 (transLenTr ⟨87, by decide⟩ 9 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 9 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_10 (hp : 10 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 10 (transLenTr ⟨87, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 10 (transLenTr ⟨87, by decide⟩ 10 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 10 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_11 (hp : 11 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 11 (transLenTr ⟨87, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 11 (transLenTr ⟨87, by decide⟩ 11 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 11 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_12 (hp : 12 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 12 (transLenTr ⟨87, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 12 (transLenTr ⟨87, by decide⟩ 12 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 12 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_13 (hp : 13 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 13 (transLenTr ⟨87, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 13 (transLenTr ⟨87, by decide⟩ 13 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 13 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_14 (hp : 14 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 14 (transLenTr ⟨87, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 14 (transLenTr ⟨87, by decide⟩ 14 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 14 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_15 (hp : 15 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 15 (transLenTr ⟨87, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 15 (transLenTr ⟨87, by decide⟩ 15 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 15 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_16 (hp : 16 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 16 (transLenTr ⟨87, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 16 (transLenTr ⟨87, by decide⟩ 16 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 16 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_17 (hp : 17 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 17 (transLenTr ⟨87, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 17 (transLenTr ⟨87, by decide⟩ 17 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 17 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_18 (hp : 18 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 18 (transLenTr ⟨87, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 18 (transLenTr ⟨87, by decide⟩ 18 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 18 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_19 (hp : 19 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 19 (transLenTr ⟨87, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 19 (transLenTr ⟨87, by decide⟩ 19 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 19 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_20 (hp : 20 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 20 (transLenTr ⟨87, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 20 (transLenTr ⟨87, by decide⟩ 20 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 20 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_21 (hp : 21 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 21 (transLenTr ⟨87, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 21 (transLenTr ⟨87, by decide⟩ 21 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 21 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_22 (hp : 22 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 22 (transLenTr ⟨87, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 22 (transLenTr ⟨87, by decide⟩ 22 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 22 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_23 (hp : 23 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 23 (transLenTr ⟨87, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 23 (transLenTr ⟨87, by decide⟩ 23 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 23 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_87_24 (hp : 24 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 24 (transLenTr ⟨87, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 24 (transLenTr ⟨87, by decide⟩ 24 hp)) T147_87
      hfix147_87 hinj147_87 hcardT147_87
      (fun i => conj_mem_of_fixedPoints _ _ (T147_87 i) (hfix147_87 i) _)
      ⟨147, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 24 hp) Q2.T147_87_2 Q2.hfix147_87_2 Q2.hinj147_87_2
      Q2.hcardT147_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_87_2 i) (Q2.hfix147_87_2 i) _)
      colCert_147_87_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_0 (hp : 0 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 0 (transLenTr ⟨88, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 0 (transLenTr ⟨88, by decide⟩ 0 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 0 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_1 (hp : 1 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 1 (transLenTr ⟨88, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 1 (transLenTr ⟨88, by decide⟩ 1 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 1 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_2 (hp : 2 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 2 (transLenTr ⟨88, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 2 (transLenTr ⟨88, by decide⟩ 2 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 2 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_3 (hp : 3 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 3 (transLenTr ⟨88, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 3 (transLenTr ⟨88, by decide⟩ 3 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 3 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_4 (hp : 4 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 4 (transLenTr ⟨88, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 4 (transLenTr ⟨88, by decide⟩ 4 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 4 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_5 (hp : 5 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 5 (transLenTr ⟨88, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 5 (transLenTr ⟨88, by decide⟩ 5 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 5 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_6 (hp : 6 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 6 (transLenTr ⟨88, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 6 (transLenTr ⟨88, by decide⟩ 6 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 6 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_7 (hp : 7 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 7 (transLenTr ⟨88, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 7 (transLenTr ⟨88, by decide⟩ 7 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 7 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_8 (hp : 8 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 8 (transLenTr ⟨88, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 8 (transLenTr ⟨88, by decide⟩ 8 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 8 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_9 (hp : 9 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 9 (transLenTr ⟨88, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 9 (transLenTr ⟨88, by decide⟩ 9 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 9 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_10 (hp : 10 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 10 (transLenTr ⟨88, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 10 (transLenTr ⟨88, by decide⟩ 10 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 10 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_11 (hp : 11 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 11 (transLenTr ⟨88, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 11 (transLenTr ⟨88, by decide⟩ 11 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 11 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_12 (hp : 12 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 12 (transLenTr ⟨88, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 12 (transLenTr ⟨88, by decide⟩ 12 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 12 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_13 (hp : 13 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 13 (transLenTr ⟨88, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 13 (transLenTr ⟨88, by decide⟩ 13 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 13 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_14 (hp : 14 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 14 (transLenTr ⟨88, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 14 (transLenTr ⟨88, by decide⟩ 14 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 14 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_15 (hp : 15 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 15 (transLenTr ⟨88, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 15 (transLenTr ⟨88, by decide⟩ 15 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 15 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_16 (hp : 16 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 16 (transLenTr ⟨88, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 16 (transLenTr ⟨88, by decide⟩ 16 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 16 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_17 (hp : 17 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 17 (transLenTr ⟨88, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 17 (transLenTr ⟨88, by decide⟩ 17 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 17 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_18 (hp : 18 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 18 (transLenTr ⟨88, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 18 (transLenTr ⟨88, by decide⟩ 18 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 18 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_19 (hp : 19 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 19 (transLenTr ⟨88, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 19 (transLenTr ⟨88, by decide⟩ 19 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 19 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_20 (hp : 20 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 20 (transLenTr ⟨88, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 20 (transLenTr ⟨88, by decide⟩ 20 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 20 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_21 (hp : 21 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 21 (transLenTr ⟨88, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 21 (transLenTr ⟨88, by decide⟩ 21 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 21 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_22 (hp : 22 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 22 (transLenTr ⟨88, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 22 (transLenTr ⟨88, by decide⟩ 22 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 22 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_23 (hp : 23 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 23 (transLenTr ⟨88, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 23 (transLenTr ⟨88, by decide⟩ 23 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 23 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_88_24 (hp : 24 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 24 (transLenTr ⟨88, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 24 (transLenTr ⟨88, by decide⟩ 24 hp)) T147_88
      hfix147_88 hinj147_88 hcardT147_88
      (fun i => conj_mem_of_fixedPoints _ _ (T147_88 i) (hfix147_88 i) _)
      ⟨147, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 24 hp) Q2.T147_88_2 Q2.hfix147_88_2 Q2.hinj147_88_2
      Q2.hcardT147_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_88_2 i) (Q2.hfix147_88_2 i) _)
      colCert_147_88_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_0 (hp : 0 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 0 (transLenTr ⟨89, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 0 (transLenTr ⟨89, by decide⟩ 0 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 0 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_1 (hp : 1 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 1 (transLenTr ⟨89, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 1 (transLenTr ⟨89, by decide⟩ 1 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 1 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_2 (hp : 2 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 2 (transLenTr ⟨89, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 2 (transLenTr ⟨89, by decide⟩ 2 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 2 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_3 (hp : 3 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 3 (transLenTr ⟨89, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 3 (transLenTr ⟨89, by decide⟩ 3 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 3 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_4 (hp : 4 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 4 (transLenTr ⟨89, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 4 (transLenTr ⟨89, by decide⟩ 4 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 4 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_5 (hp : 5 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 5 (transLenTr ⟨89, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 5 (transLenTr ⟨89, by decide⟩ 5 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 5 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_6 (hp : 6 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 6 (transLenTr ⟨89, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 6 (transLenTr ⟨89, by decide⟩ 6 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 6 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_7 (hp : 7 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 7 (transLenTr ⟨89, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 7 (transLenTr ⟨89, by decide⟩ 7 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 7 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_8 (hp : 8 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 8 (transLenTr ⟨89, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 8 (transLenTr ⟨89, by decide⟩ 8 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 8 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_9 (hp : 9 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 9 (transLenTr ⟨89, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 9 (transLenTr ⟨89, by decide⟩ 9 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 9 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_10 (hp : 10 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 10 (transLenTr ⟨89, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 10 (transLenTr ⟨89, by decide⟩ 10 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 10 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_11 (hp : 11 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 11 (transLenTr ⟨89, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 11 (transLenTr ⟨89, by decide⟩ 11 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 11 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_12 (hp : 12 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 12 (transLenTr ⟨89, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 12 (transLenTr ⟨89, by decide⟩ 12 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 12 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_13 (hp : 13 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 13 (transLenTr ⟨89, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 13 (transLenTr ⟨89, by decide⟩ 13 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 13 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_14 (hp : 14 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 14 (transLenTr ⟨89, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 14 (transLenTr ⟨89, by decide⟩ 14 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 14 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_15 (hp : 15 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 15 (transLenTr ⟨89, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 15 (transLenTr ⟨89, by decide⟩ 15 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 15 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_16 (hp : 16 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 16 (transLenTr ⟨89, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 16 (transLenTr ⟨89, by decide⟩ 16 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 16 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_17 (hp : 17 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 17 (transLenTr ⟨89, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 17 (transLenTr ⟨89, by decide⟩ 17 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 17 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_18 (hp : 18 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 18 (transLenTr ⟨89, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 18 (transLenTr ⟨89, by decide⟩ 18 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 18 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_19 (hp : 19 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 19 (transLenTr ⟨89, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 19 (transLenTr ⟨89, by decide⟩ 19 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 19 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_20 (hp : 20 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 20 (transLenTr ⟨89, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 20 (transLenTr ⟨89, by decide⟩ 20 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 20 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_21 (hp : 21 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 21 (transLenTr ⟨89, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 21 (transLenTr ⟨89, by decide⟩ 21 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 21 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_22 (hp : 22 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 22 (transLenTr ⟨89, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 22 (transLenTr ⟨89, by decide⟩ 22 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 22 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_23 (hp : 23 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 23 (transLenTr ⟨89, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 23 (transLenTr ⟨89, by decide⟩ 23 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 23 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_89_24 (hp : 24 < (Q2.transData.getD 89 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ 24 (transLenTr ⟨89, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨89, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨89, by decide⟩ 24 (transLenTr ⟨89, by decide⟩ 24 hp)) T147_89
      hfix147_89 hinj147_89 hcardT147_89
      (fun i => conj_mem_of_fixedPoints _ _ (T147_89 i) (hfix147_89 i) _)
      ⟨147, by decide⟩ ⟨89, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨89, by decide⟩ 24 hp) Q2.T147_89_2 Q2.hfix147_89_2 Q2.hinj147_89_2
      Q2.hcardT147_89_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_89_2 i) (Q2.hfix147_89_2 i) _)
      colCert_147_89_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_0 (hp : 0 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 0 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_1 (hp : 1 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 1 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_2 (hp : 2 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 2 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_3 (hp : 3 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 3 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_4 (hp : 4 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 4 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_5 (hp : 5 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 5 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_10 (hp : 10 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 10 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_15 (hp : 15 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 15 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_20 (hp : 20 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 20 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_25 (hp : 25 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 25 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_50 (hp : 50 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 50 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_75 (hp : 75 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 75 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_75.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_90_100 (hp : 100 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp)) T147_90
      hfix147_90 hinj147_90 hcardT147_90
      (fun i => conj_mem_of_fixedPoints _ _ (T147_90 i) (hfix147_90 i) _)
      ⟨147, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 100 hp) Q2.T147_90_2 Q2.hfix147_90_2 Q2.hinj147_90_2
      Q2.hcardT147_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_90_2 i) (Q2.hfix147_90_2 i) _)
      colCert_147_90_100.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_91_0 (hp : 0 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp)) T147_91
      hfix147_91 hinj147_91 hcardT147_91
      (fun i => conj_mem_of_fixedPoints _ _ (T147_91 i) (hfix147_91 i) _)
      ⟨147, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 0 hp) Q2.T147_91_2 Q2.hfix147_91_2 Q2.hinj147_91_2
      Q2.hcardT147_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_91_2 i) (Q2.hfix147_91_2 i) _)
      colCert_147_91_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_91_1 (hp : 1 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp)) T147_91
      hfix147_91 hinj147_91 hcardT147_91
      (fun i => conj_mem_of_fixedPoints _ _ (T147_91 i) (hfix147_91 i) _)
      ⟨147, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 1 hp) Q2.T147_91_2 Q2.hfix147_91_2 Q2.hinj147_91_2
      Q2.hcardT147_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_91_2 i) (Q2.hfix147_91_2 i) _)
      colCert_147_91_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_91_2 (hp : 2 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp)) T147_91
      hfix147_91 hinj147_91 hcardT147_91
      (fun i => conj_mem_of_fixedPoints _ _ (T147_91 i) (hfix147_91 i) _)
      ⟨147, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 2 hp) Q2.T147_91_2 Q2.hfix147_91_2 Q2.hinj147_91_2
      Q2.hcardT147_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_91_2 i) (Q2.hfix147_91_2 i) _)
      colCert_147_91_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_91_3 (hp : 3 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp)) T147_91
      hfix147_91 hinj147_91 hcardT147_91
      (fun i => conj_mem_of_fixedPoints _ _ (T147_91 i) (hfix147_91 i) _)
      ⟨147, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 3 hp) Q2.T147_91_2 Q2.hfix147_91_2 Q2.hinj147_91_2
      Q2.hcardT147_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_91_2 i) (Q2.hfix147_91_2 i) _)
      colCert_147_91_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_91_4 (hp : 4 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp)) T147_91
      hfix147_91 hinj147_91 hcardT147_91
      (fun i => conj_mem_of_fixedPoints _ _ (T147_91 i) (hfix147_91 i) _)
      ⟨147, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 4 hp) Q2.T147_91_2 Q2.hfix147_91_2 Q2.hinj147_91_2
      Q2.hcardT147_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_91_2 i) (Q2.hfix147_91_2 i) _)
      colCert_147_91_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_91_5 (hp : 5 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp)) T147_91
      hfix147_91 hinj147_91 hcardT147_91
      (fun i => conj_mem_of_fixedPoints _ _ (T147_91 i) (hfix147_91 i) _)
      ⟨147, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 5 hp) Q2.T147_91_2 Q2.hfix147_91_2 Q2.hinj147_91_2
      Q2.hcardT147_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_91_2 i) (Q2.hfix147_91_2 i) _)
      colCert_147_91_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_91_10 (hp : 10 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp)) T147_91
      hfix147_91 hinj147_91 hcardT147_91
      (fun i => conj_mem_of_fixedPoints _ _ (T147_91 i) (hfix147_91 i) _)
      ⟨147, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 10 hp) Q2.T147_91_2 Q2.hfix147_91_2 Q2.hinj147_91_2
      Q2.hcardT147_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_91_2 i) (Q2.hfix147_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T147_91 = colFn colCertDiv_147_91_10.D1 (m := 1) from colCertDiv_147_91_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 10 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T147_91_2 = colFn colCertDiv_147_91_10.D2 (m := 1) from colCertDiv_147_91_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_91_10_match


theorem leaf_147_91_15 (hp : 15 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp)) T147_91
      hfix147_91 hinj147_91 hcardT147_91
      (fun i => conj_mem_of_fixedPoints _ _ (T147_91 i) (hfix147_91 i) _)
      ⟨147, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 15 hp) Q2.T147_91_2 Q2.hfix147_91_2 Q2.hinj147_91_2
      Q2.hcardT147_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_91_2 i) (Q2.hfix147_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T147_91 = colFn colCertDiv_147_91_15.D1 (m := 1) from colCertDiv_147_91_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 15 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T147_91_2 = colFn colCertDiv_147_91_15.D2 (m := 1) from colCertDiv_147_91_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_91_15_match


theorem leaf_147_91_20 (hp : 20 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp)) T147_91
      hfix147_91 hinj147_91 hcardT147_91
      (fun i => conj_mem_of_fixedPoints _ _ (T147_91 i) (hfix147_91 i) _)
      ⟨147, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 20 hp) Q2.T147_91_2 Q2.hfix147_91_2 Q2.hinj147_91_2
      Q2.hcardT147_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_91_2 i) (Q2.hfix147_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T147_91 = colFn colCertDiv_147_91_20.D1 (m := 1) from colCertDiv_147_91_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 20 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T147_91_2 = colFn colCertDiv_147_91_20.D2 (m := 1) from colCertDiv_147_91_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_91_20_match


theorem leaf_147_92_0 (hp : 0 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp)) T147_92
      hfix147_92 hinj147_92 hcardT147_92
      (fun i => conj_mem_of_fixedPoints _ _ (T147_92 i) (hfix147_92 i) _)
      ⟨147, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 0 hp) Q2.T147_92_2 Q2.hfix147_92_2 Q2.hinj147_92_2
      Q2.hcardT147_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_92_2 i) (Q2.hfix147_92_2 i) _)
      colCert_147_92_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_92_1 (hp : 1 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp)) T147_92
      hfix147_92 hinj147_92 hcardT147_92
      (fun i => conj_mem_of_fixedPoints _ _ (T147_92 i) (hfix147_92 i) _)
      ⟨147, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 1 hp) Q2.T147_92_2 Q2.hfix147_92_2 Q2.hinj147_92_2
      Q2.hcardT147_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_92_2 i) (Q2.hfix147_92_2 i) _)
      colCert_147_92_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_92_2 (hp : 2 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp)) T147_92
      hfix147_92 hinj147_92 hcardT147_92
      (fun i => conj_mem_of_fixedPoints _ _ (T147_92 i) (hfix147_92 i) _)
      ⟨147, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 2 hp) Q2.T147_92_2 Q2.hfix147_92_2 Q2.hinj147_92_2
      Q2.hcardT147_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_92_2 i) (Q2.hfix147_92_2 i) _)
      colCert_147_92_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_92_3 (hp : 3 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp)) T147_92
      hfix147_92 hinj147_92 hcardT147_92
      (fun i => conj_mem_of_fixedPoints _ _ (T147_92 i) (hfix147_92 i) _)
      ⟨147, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 3 hp) Q2.T147_92_2 Q2.hfix147_92_2 Q2.hinj147_92_2
      Q2.hcardT147_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_92_2 i) (Q2.hfix147_92_2 i) _)
      colCert_147_92_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_92_4 (hp : 4 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp)) T147_92
      hfix147_92 hinj147_92 hcardT147_92
      (fun i => conj_mem_of_fixedPoints _ _ (T147_92 i) (hfix147_92 i) _)
      ⟨147, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 4 hp) Q2.T147_92_2 Q2.hfix147_92_2 Q2.hinj147_92_2
      Q2.hcardT147_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_92_2 i) (Q2.hfix147_92_2 i) _)
      colCert_147_92_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_92_5 (hp : 5 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp)) T147_92
      hfix147_92 hinj147_92 hcardT147_92
      (fun i => conj_mem_of_fixedPoints _ _ (T147_92 i) (hfix147_92 i) _)
      ⟨147, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 5 hp) Q2.T147_92_2 Q2.hfix147_92_2 Q2.hinj147_92_2
      Q2.hcardT147_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_92_2 i) (Q2.hfix147_92_2 i) _)
      colCert_147_92_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_92_10 (hp : 10 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp)) T147_92
      hfix147_92 hinj147_92 hcardT147_92
      (fun i => conj_mem_of_fixedPoints _ _ (T147_92 i) (hfix147_92 i) _)
      ⟨147, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 10 hp) Q2.T147_92_2 Q2.hfix147_92_2 Q2.hinj147_92_2
      Q2.hcardT147_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_92_2 i) (Q2.hfix147_92_2 i) _)
      colCert_147_92_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_92_15 (hp : 15 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp)) T147_92
      hfix147_92 hinj147_92 hcardT147_92
      (fun i => conj_mem_of_fixedPoints _ _ (T147_92 i) (hfix147_92 i) _)
      ⟨147, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 15 hp) Q2.T147_92_2 Q2.hfix147_92_2 Q2.hinj147_92_2
      Q2.hcardT147_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_92_2 i) (Q2.hfix147_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T147_92 = colFn colCertDiv_147_92_15.D1 (m := 1) from colCertDiv_147_92_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 15 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T147_92_2 = colFn colCertDiv_147_92_15.D2 (m := 1) from colCertDiv_147_92_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_92_15_match


theorem leaf_147_92_20 (hp : 20 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp)) T147_92
      hfix147_92 hinj147_92 hcardT147_92
      (fun i => conj_mem_of_fixedPoints _ _ (T147_92 i) (hfix147_92 i) _)
      ⟨147, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 20 hp) Q2.T147_92_2 Q2.hfix147_92_2 Q2.hinj147_92_2
      Q2.hcardT147_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_92_2 i) (Q2.hfix147_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T147_92 = colFn colCertDiv_147_92_20.D1 (m := 1) from colCertDiv_147_92_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 20 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T147_92_2 = colFn colCertDiv_147_92_20.D2 (m := 1) from colCertDiv_147_92_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_92_20_match


theorem leaf_147_93_0 (hp : 0 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp)) T147_93
      hfix147_93 hinj147_93 hcardT147_93
      (fun i => conj_mem_of_fixedPoints _ _ (T147_93 i) (hfix147_93 i) _)
      ⟨147, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 0 hp) Q2.T147_93_2 Q2.hfix147_93_2 Q2.hinj147_93_2
      Q2.hcardT147_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_93_2 i) (Q2.hfix147_93_2 i) _)
      colCert_147_93_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_93_1 (hp : 1 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp)) T147_93
      hfix147_93 hinj147_93 hcardT147_93
      (fun i => conj_mem_of_fixedPoints _ _ (T147_93 i) (hfix147_93 i) _)
      ⟨147, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 1 hp) Q2.T147_93_2 Q2.hfix147_93_2 Q2.hinj147_93_2
      Q2.hcardT147_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_93_2 i) (Q2.hfix147_93_2 i) _)
      colCert_147_93_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_93_2 (hp : 2 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp)) T147_93
      hfix147_93 hinj147_93 hcardT147_93
      (fun i => conj_mem_of_fixedPoints _ _ (T147_93 i) (hfix147_93 i) _)
      ⟨147, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 2 hp) Q2.T147_93_2 Q2.hfix147_93_2 Q2.hinj147_93_2
      Q2.hcardT147_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_93_2 i) (Q2.hfix147_93_2 i) _)
      colCert_147_93_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_93_3 (hp : 3 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp)) T147_93
      hfix147_93 hinj147_93 hcardT147_93
      (fun i => conj_mem_of_fixedPoints _ _ (T147_93 i) (hfix147_93 i) _)
      ⟨147, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 3 hp) Q2.T147_93_2 Q2.hfix147_93_2 Q2.hinj147_93_2
      Q2.hcardT147_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_93_2 i) (Q2.hfix147_93_2 i) _)
      colCert_147_93_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_93_4 (hp : 4 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp)) T147_93
      hfix147_93 hinj147_93 hcardT147_93
      (fun i => conj_mem_of_fixedPoints _ _ (T147_93 i) (hfix147_93 i) _)
      ⟨147, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 4 hp) Q2.T147_93_2 Q2.hfix147_93_2 Q2.hinj147_93_2
      Q2.hcardT147_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_93_2 i) (Q2.hfix147_93_2 i) _)
      colCert_147_93_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_93_5 (hp : 5 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp)) T147_93
      hfix147_93 hinj147_93 hcardT147_93
      (fun i => conj_mem_of_fixedPoints _ _ (T147_93 i) (hfix147_93 i) _)
      ⟨147, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 5 hp) Q2.T147_93_2 Q2.hfix147_93_2 Q2.hinj147_93_2
      Q2.hcardT147_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_93_2 i) (Q2.hfix147_93_2 i) _)
      colCert_147_93_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_93_10 (hp : 10 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp)) T147_93
      hfix147_93 hinj147_93 hcardT147_93
      (fun i => conj_mem_of_fixedPoints _ _ (T147_93 i) (hfix147_93 i) _)
      ⟨147, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 10 hp) Q2.T147_93_2 Q2.hfix147_93_2 Q2.hinj147_93_2
      Q2.hcardT147_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_93_2 i) (Q2.hfix147_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T147_93 = colFn colCertDiv_147_93_10.D1 (m := 1) from colCertDiv_147_93_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 10 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T147_93_2 = colFn colCertDiv_147_93_10.D2 (m := 1) from colCertDiv_147_93_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_93_10_match


theorem leaf_147_93_15 (hp : 15 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp)) T147_93
      hfix147_93 hinj147_93 hcardT147_93
      (fun i => conj_mem_of_fixedPoints _ _ (T147_93 i) (hfix147_93 i) _)
      ⟨147, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 15 hp) Q2.T147_93_2 Q2.hfix147_93_2 Q2.hinj147_93_2
      Q2.hcardT147_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_93_2 i) (Q2.hfix147_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T147_93 = colFn colCertDiv_147_93_15.D1 (m := 1) from colCertDiv_147_93_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 15 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T147_93_2 = colFn colCertDiv_147_93_15.D2 (m := 1) from colCertDiv_147_93_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_93_15_match


theorem leaf_147_93_20 (hp : 20 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp)) T147_93
      hfix147_93 hinj147_93 hcardT147_93
      (fun i => conj_mem_of_fixedPoints _ _ (T147_93 i) (hfix147_93 i) _)
      ⟨147, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 20 hp) Q2.T147_93_2 Q2.hfix147_93_2 Q2.hinj147_93_2
      Q2.hcardT147_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_93_2 i) (Q2.hfix147_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T147_93 = colFn colCertDiv_147_93_20.D1 (m := 1) from colCertDiv_147_93_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 20 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T147_93_2 = colFn colCertDiv_147_93_20.D2 (m := 1) from colCertDiv_147_93_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_93_20_match


theorem leaf_147_94_0 (hp : 0 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 0 (transLenTr ⟨94, by decide⟩ 0 hp)) T147_94
      hfix147_94 hinj147_94 hcardT147_94
      (fun i => conj_mem_of_fixedPoints _ _ (T147_94 i) (hfix147_94 i) _)
      ⟨147, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 0 hp) Q2.T147_94_2 Q2.hfix147_94_2 Q2.hinj147_94_2
      Q2.hcardT147_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_94_2 i) (Q2.hfix147_94_2 i) _)
      colCert_147_94_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_94_1 (hp : 1 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 1 (transLenTr ⟨94, by decide⟩ 1 hp)) T147_94
      hfix147_94 hinj147_94 hcardT147_94
      (fun i => conj_mem_of_fixedPoints _ _ (T147_94 i) (hfix147_94 i) _)
      ⟨147, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 1 hp) Q2.T147_94_2 Q2.hfix147_94_2 Q2.hinj147_94_2
      Q2.hcardT147_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_94_2 i) (Q2.hfix147_94_2 i) _)
      colCert_147_94_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_94_2 (hp : 2 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 2 (transLenTr ⟨94, by decide⟩ 2 hp)) T147_94
      hfix147_94 hinj147_94 hcardT147_94
      (fun i => conj_mem_of_fixedPoints _ _ (T147_94 i) (hfix147_94 i) _)
      ⟨147, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 2 hp) Q2.T147_94_2 Q2.hfix147_94_2 Q2.hinj147_94_2
      Q2.hcardT147_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_94_2 i) (Q2.hfix147_94_2 i) _)
      colCert_147_94_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_94_3 (hp : 3 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 3 (transLenTr ⟨94, by decide⟩ 3 hp)) T147_94
      hfix147_94 hinj147_94 hcardT147_94
      (fun i => conj_mem_of_fixedPoints _ _ (T147_94 i) (hfix147_94 i) _)
      ⟨147, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 3 hp) Q2.T147_94_2 Q2.hfix147_94_2 Q2.hinj147_94_2
      Q2.hcardT147_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_94_2 i) (Q2.hfix147_94_2 i) _)
      colCert_147_94_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_94_4 (hp : 4 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 4 (transLenTr ⟨94, by decide⟩ 4 hp)) T147_94
      hfix147_94 hinj147_94 hcardT147_94
      (fun i => conj_mem_of_fixedPoints _ _ (T147_94 i) (hfix147_94 i) _)
      ⟨147, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 4 hp) Q2.T147_94_2 Q2.hfix147_94_2 Q2.hinj147_94_2
      Q2.hcardT147_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_94_2 i) (Q2.hfix147_94_2 i) _)
      colCert_147_94_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_94_5 (hp : 5 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 5 (transLenTr ⟨94, by decide⟩ 5 hp)) T147_94
      hfix147_94 hinj147_94 hcardT147_94
      (fun i => conj_mem_of_fixedPoints _ _ (T147_94 i) (hfix147_94 i) _)
      ⟨147, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 5 hp) Q2.T147_94_2 Q2.hfix147_94_2 Q2.hinj147_94_2
      Q2.hcardT147_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_94_2 i) (Q2.hfix147_94_2 i) _)
      colCert_147_94_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_94_10 (hp : 10 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 10 (transLenTr ⟨94, by decide⟩ 10 hp)) T147_94
      hfix147_94 hinj147_94 hcardT147_94
      (fun i => conj_mem_of_fixedPoints _ _ (T147_94 i) (hfix147_94 i) _)
      ⟨147, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 10 hp) Q2.T147_94_2 Q2.hfix147_94_2 Q2.hinj147_94_2
      Q2.hcardT147_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_94_2 i) (Q2.hfix147_94_2 i) _)
      colCert_147_94_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_94_15 (hp : 15 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 15 (transLenTr ⟨94, by decide⟩ 15 hp)) T147_94
      hfix147_94 hinj147_94 hcardT147_94
      (fun i => conj_mem_of_fixedPoints _ _ (T147_94 i) (hfix147_94 i) _)
      ⟨147, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 15 hp) Q2.T147_94_2 Q2.hfix147_94_2 Q2.hinj147_94_2
      Q2.hcardT147_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_94_2 i) (Q2.hfix147_94_2 i) _)
      colCert_147_94_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_94_20 (hp : 20 < (Q2.transData.getD 94 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨94, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨94, by decide⟩ 20 (transLenTr ⟨94, by decide⟩ 20 hp)) T147_94
      hfix147_94 hinj147_94 hcardT147_94
      (fun i => conj_mem_of_fixedPoints _ _ (T147_94 i) (hfix147_94 i) _)
      ⟨147, by decide⟩ ⟨94, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨94, by decide⟩ 20 hp) Q2.T147_94_2 Q2.hfix147_94_2 Q2.hinj147_94_2
      Q2.hcardT147_94_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_94_2 i) (Q2.hfix147_94_2 i) _)
      colCert_147_94_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_0 (hp : 0 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 0 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_1 (hp : 1 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 1 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_2 (hp : 2 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 2 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_3 (hp : 3 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 3 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_4 (hp : 4 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 4 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_5 (hp : 5 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 5 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_10 (hp : 10 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 10 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_15 (hp : 15 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 15 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_20 (hp : 20 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 20 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_25 (hp : 25 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 25 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_50 (hp : 50 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 50 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_75 (hp : 75 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 75 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_75.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_95_100 (hp : 100 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp)) T147_95
      hfix147_95 hinj147_95 hcardT147_95
      (fun i => conj_mem_of_fixedPoints _ _ (T147_95 i) (hfix147_95 i) _)
      ⟨147, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 100 hp) Q2.T147_95_2 Q2.hfix147_95_2 Q2.hinj147_95_2
      Q2.hcardT147_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_95_2 i) (Q2.hfix147_95_2 i) _)
      colCert_147_95_100.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_96_0 (hp : 0 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp)) T147_96
      hfix147_96 hinj147_96 hcardT147_96
      (fun i => conj_mem_of_fixedPoints _ _ (T147_96 i) (hfix147_96 i) _)
      ⟨147, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 0 hp) Q2.T147_96_2 Q2.hfix147_96_2 Q2.hinj147_96_2
      Q2.hcardT147_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_96_2 i) (Q2.hfix147_96_2 i) _)
      colCert_147_96_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_96_1 (hp : 1 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp)) T147_96
      hfix147_96 hinj147_96 hcardT147_96
      (fun i => conj_mem_of_fixedPoints _ _ (T147_96 i) (hfix147_96 i) _)
      ⟨147, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 1 hp) Q2.T147_96_2 Q2.hfix147_96_2 Q2.hinj147_96_2
      Q2.hcardT147_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_96_2 i) (Q2.hfix147_96_2 i) _)
      colCert_147_96_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_96_2 (hp : 2 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp)) T147_96
      hfix147_96 hinj147_96 hcardT147_96
      (fun i => conj_mem_of_fixedPoints _ _ (T147_96 i) (hfix147_96 i) _)
      ⟨147, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 2 hp) Q2.T147_96_2 Q2.hfix147_96_2 Q2.hinj147_96_2
      Q2.hcardT147_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_96_2 i) (Q2.hfix147_96_2 i) _)
      colCert_147_96_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_96_3 (hp : 3 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp)) T147_96
      hfix147_96 hinj147_96 hcardT147_96
      (fun i => conj_mem_of_fixedPoints _ _ (T147_96 i) (hfix147_96 i) _)
      ⟨147, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 3 hp) Q2.T147_96_2 Q2.hfix147_96_2 Q2.hinj147_96_2
      Q2.hcardT147_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_96_2 i) (Q2.hfix147_96_2 i) _)
      colCert_147_96_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_96_4 (hp : 4 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp)) T147_96
      hfix147_96 hinj147_96 hcardT147_96
      (fun i => conj_mem_of_fixedPoints _ _ (T147_96 i) (hfix147_96 i) _)
      ⟨147, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 4 hp) Q2.T147_96_2 Q2.hfix147_96_2 Q2.hinj147_96_2
      Q2.hcardT147_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_96_2 i) (Q2.hfix147_96_2 i) _)
      colCert_147_96_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_96_5 (hp : 5 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp)) T147_96
      hfix147_96 hinj147_96 hcardT147_96
      (fun i => conj_mem_of_fixedPoints _ _ (T147_96 i) (hfix147_96 i) _)
      ⟨147, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 5 hp) Q2.T147_96_2 Q2.hfix147_96_2 Q2.hinj147_96_2
      Q2.hcardT147_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_96_2 i) (Q2.hfix147_96_2 i) _)
      colCert_147_96_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_96_10 (hp : 10 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp)) T147_96
      hfix147_96 hinj147_96 hcardT147_96
      (fun i => conj_mem_of_fixedPoints _ _ (T147_96 i) (hfix147_96 i) _)
      ⟨147, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 10 hp) Q2.T147_96_2 Q2.hfix147_96_2 Q2.hinj147_96_2
      Q2.hcardT147_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_96_2 i) (Q2.hfix147_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T147_96 = colFn colCertDiv_147_96_10.D1 (m := 1) from colCertDiv_147_96_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 10 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T147_96_2 = colFn colCertDiv_147_96_10.D2 (m := 1) from colCertDiv_147_96_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_96_10_match


theorem leaf_147_96_15 (hp : 15 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp)) T147_96
      hfix147_96 hinj147_96 hcardT147_96
      (fun i => conj_mem_of_fixedPoints _ _ (T147_96 i) (hfix147_96 i) _)
      ⟨147, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 15 hp) Q2.T147_96_2 Q2.hfix147_96_2 Q2.hinj147_96_2
      Q2.hcardT147_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_96_2 i) (Q2.hfix147_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T147_96 = colFn colCertDiv_147_96_15.D1 (m := 1) from colCertDiv_147_96_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 15 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T147_96_2 = colFn colCertDiv_147_96_15.D2 (m := 1) from colCertDiv_147_96_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_96_15_match


theorem leaf_147_96_20 (hp : 20 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp)) T147_96
      hfix147_96 hinj147_96 hcardT147_96
      (fun i => conj_mem_of_fixedPoints _ _ (T147_96 i) (hfix147_96 i) _)
      ⟨147, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 20 hp) Q2.T147_96_2 Q2.hfix147_96_2 Q2.hinj147_96_2
      Q2.hcardT147_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_96_2 i) (Q2.hfix147_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T147_96 = colFn colCertDiv_147_96_20.D1 (m := 1) from colCertDiv_147_96_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 20 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T147_96_2 = colFn colCertDiv_147_96_20.D2 (m := 1) from colCertDiv_147_96_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_96_20_match


end LeanDring.P5Presentation
