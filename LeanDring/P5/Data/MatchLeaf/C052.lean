/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C026
import LeanDring.P5.Data.ColCdd.C027
import LeanDring.P5.Data.ColCdd.C028
import LeanDring.P5.Data.ColCdd.C029
import LeanDring.P5.Data.ColRestCheap.C117
import LeanDring.P5.Data.ColRestCheap.C118
import LeanDring.P5.Data.ColRestCheap.C119
import LeanDring.P5.Data.ColTau.C003
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C038
import LeanDring.P5.Data.SpeciesDiv.C039
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk03

/-! # Stage-5 leaves, chunk 51 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_147_64_11 (hp : 11 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 11 (transLenTr ⟨64, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 11 (transLenTr ⟨64, by decide⟩ 11 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 11 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_12 (hp : 12 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 12 (transLenTr ⟨64, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 12 (transLenTr ⟨64, by decide⟩ 12 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 12 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_13 (hp : 13 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 13 (transLenTr ⟨64, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 13 (transLenTr ⟨64, by decide⟩ 13 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 13 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_14 (hp : 14 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 14 (transLenTr ⟨64, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 14 (transLenTr ⟨64, by decide⟩ 14 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 14 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_15 (hp : 15 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 15 (transLenTr ⟨64, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 15 (transLenTr ⟨64, by decide⟩ 15 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 15 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_16 (hp : 16 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 16 (transLenTr ⟨64, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 16 (transLenTr ⟨64, by decide⟩ 16 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 16 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_17 (hp : 17 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 17 (transLenTr ⟨64, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 17 (transLenTr ⟨64, by decide⟩ 17 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 17 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_18 (hp : 18 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 18 (transLenTr ⟨64, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 18 (transLenTr ⟨64, by decide⟩ 18 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 18 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_19 (hp : 19 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 19 (transLenTr ⟨64, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 19 (transLenTr ⟨64, by decide⟩ 19 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 19 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_20 (hp : 20 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 20 (transLenTr ⟨64, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 20 (transLenTr ⟨64, by decide⟩ 20 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 20 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_21 (hp : 21 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 21 (transLenTr ⟨64, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 21 (transLenTr ⟨64, by decide⟩ 21 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 21 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_22 (hp : 22 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 22 (transLenTr ⟨64, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 22 (transLenTr ⟨64, by decide⟩ 22 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 22 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_23 (hp : 23 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 23 (transLenTr ⟨64, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 23 (transLenTr ⟨64, by decide⟩ 23 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 23 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_24 (hp : 24 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 24 (transLenTr ⟨64, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 24 (transLenTr ⟨64, by decide⟩ 24 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 24 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_25 (hp : 25 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 25 (transLenTr ⟨64, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 25 (transLenTr ⟨64, by decide⟩ 25 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 25 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_30 (hp : 30 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 30 (transLenTr ⟨64, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 30 (transLenTr ⟨64, by decide⟩ 30 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 30 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_35 (hp : 35 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 35 (transLenTr ⟨64, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 35 (transLenTr ⟨64, by decide⟩ 35 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 35 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_40 (hp : 40 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 40 (transLenTr ⟨64, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 40 (transLenTr ⟨64, by decide⟩ 40 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 40 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_45 (hp : 45 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 45 (transLenTr ⟨64, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 45 (transLenTr ⟨64, by decide⟩ 45 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 45 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_50 (hp : 50 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 50 (transLenTr ⟨64, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 50 (transLenTr ⟨64, by decide⟩ 50 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 50 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 50 (transLenTr ⟨64, by decide⟩ 50 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_50.D1 (m := 1) from colCertDiv_147_64_50.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 50 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_50.D2 (m := 1) from colCertDiv_147_64_50.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_50_match


theorem leaf_147_64_55 (hp : 55 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 55 (transLenTr ⟨64, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 55 (transLenTr ⟨64, by decide⟩ 55 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 55 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 55 (transLenTr ⟨64, by decide⟩ 55 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_55.D1 (m := 1) from colCertDiv_147_64_55.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 55 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_55.D2 (m := 1) from colCertDiv_147_64_55.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_55_match


theorem leaf_147_64_60 (hp : 60 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 60 (transLenTr ⟨64, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 60 (transLenTr ⟨64, by decide⟩ 60 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 60 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 60 (transLenTr ⟨64, by decide⟩ 60 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_60.D1 (m := 1) from colCertDiv_147_64_60.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 60 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_60.D2 (m := 1) from colCertDiv_147_64_60.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_60_match


theorem leaf_147_64_65 (hp : 65 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 65 (transLenTr ⟨64, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 65 (transLenTr ⟨64, by decide⟩ 65 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 65 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 65 (transLenTr ⟨64, by decide⟩ 65 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_65.D1 (m := 1) from colCertDiv_147_64_65.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 65 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_65.D2 (m := 1) from colCertDiv_147_64_65.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_65_match


theorem leaf_147_64_70 (hp : 70 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 70 (transLenTr ⟨64, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 70 (transLenTr ⟨64, by decide⟩ 70 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 70 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 70 (transLenTr ⟨64, by decide⟩ 70 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_70.D1 (m := 1) from colCertDiv_147_64_70.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 70 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_70.D2 (m := 1) from colCertDiv_147_64_70.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_70_match


theorem leaf_147_64_75 (hp : 75 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 75 (transLenTr ⟨64, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 75 (transLenTr ⟨64, by decide⟩ 75 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 75 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 75 (transLenTr ⟨64, by decide⟩ 75 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_75.D1 (m := 1) from colCertDiv_147_64_75.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 75 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_75.D2 (m := 1) from colCertDiv_147_64_75.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_75_match


theorem leaf_147_64_80 (hp : 80 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 80 (transLenTr ⟨64, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 80 (transLenTr ⟨64, by decide⟩ 80 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 80 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 80 (transLenTr ⟨64, by decide⟩ 80 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_80.D1 (m := 1) from colCertDiv_147_64_80.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 80 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_80.D2 (m := 1) from colCertDiv_147_64_80.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_80_match


theorem leaf_147_64_85 (hp : 85 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 85 (transLenTr ⟨64, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 85 (transLenTr ⟨64, by decide⟩ 85 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 85 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 85 (transLenTr ⟨64, by decide⟩ 85 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_85.D1 (m := 1) from colCertDiv_147_64_85.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 85 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_85.D2 (m := 1) from colCertDiv_147_64_85.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_85_match


theorem leaf_147_64_90 (hp : 90 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 90 (transLenTr ⟨64, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 90 (transLenTr ⟨64, by decide⟩ 90 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 90 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 90 (transLenTr ⟨64, by decide⟩ 90 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_90.D1 (m := 1) from colCertDiv_147_64_90.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 90 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_90.D2 (m := 1) from colCertDiv_147_64_90.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_90_match


theorem leaf_147_64_95 (hp : 95 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 95 (transLenTr ⟨64, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 95 (transLenTr ⟨64, by decide⟩ 95 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 95 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 95 (transLenTr ⟨64, by decide⟩ 95 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_95.D1 (m := 1) from colCertDiv_147_64_95.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 95 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_95.D2 (m := 1) from colCertDiv_147_64_95.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_95_match


theorem leaf_147_64_100 (hp : 100 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 100 (transLenTr ⟨64, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 100 (transLenTr ⟨64, by decide⟩ 100 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 100 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 100 (transLenTr ⟨64, by decide⟩ 100 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_100.D1 (m := 1) from colCertDiv_147_64_100.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 100 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_100.D2 (m := 1) from colCertDiv_147_64_100.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_100_match


theorem leaf_147_64_105 (hp : 105 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 105 (transLenTr ⟨64, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 105 (transLenTr ⟨64, by decide⟩ 105 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 105 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 105 (transLenTr ⟨64, by decide⟩ 105 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_105.D1 (m := 1) from colCertDiv_147_64_105.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 105 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_105.D2 (m := 1) from colCertDiv_147_64_105.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_105_match


theorem leaf_147_64_110 (hp : 110 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 110 (transLenTr ⟨64, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 110 (transLenTr ⟨64, by decide⟩ 110 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 110 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 110 (transLenTr ⟨64, by decide⟩ 110 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_110.D1 (m := 1) from colCertDiv_147_64_110.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 110 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_110.D2 (m := 1) from colCertDiv_147_64_110.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_110_match


theorem leaf_147_64_115 (hp : 115 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 115 (transLenTr ⟨64, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 115 (transLenTr ⟨64, by decide⟩ 115 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 115 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 115 (transLenTr ⟨64, by decide⟩ 115 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_115.D1 (m := 1) from colCertDiv_147_64_115.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 115 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_115.D2 (m := 1) from colCertDiv_147_64_115.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_115_match


theorem leaf_147_64_120 (hp : 120 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 120 (transLenTr ⟨64, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 120 (transLenTr ⟨64, by decide⟩ 120 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 120 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨64, by decide⟩ 120 (transLenTr ⟨64, by decide⟩ 120 hp) : ↥(reps ⟨64, by decide⟩)) : Coordinate 1)
        T147_64 = colFn colCertDiv_147_64_120.D1 (m := 1) from colCertDiv_147_64_120.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨64, by decide⟩ 120 hp : ↥(Q2.reps ⟨64, by decide⟩)) : Coordinate 2)
        Q2.T147_64_2 = colFn colCertDiv_147_64_120.D2 (m := 1) from colCertDiv_147_64_120.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_64_120_match


theorem leaf_147_65_0 (hp : 0 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 0 (transLenTr ⟨65, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 0 (transLenTr ⟨65, by decide⟩ 0 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 0 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      colCert_147_65_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_65_1 (hp : 1 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 1 (transLenTr ⟨65, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 1 (transLenTr ⟨65, by decide⟩ 1 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 1 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      colCert_147_65_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_65_2 (hp : 2 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 2 (transLenTr ⟨65, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 2 (transLenTr ⟨65, by decide⟩ 2 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 2 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      colCert_147_65_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_65_3 (hp : 3 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 3 (transLenTr ⟨65, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 3 (transLenTr ⟨65, by decide⟩ 3 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 3 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      colCert_147_65_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_65_4 (hp : 4 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 4 (transLenTr ⟨65, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 4 (transLenTr ⟨65, by decide⟩ 4 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 4 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      colCert_147_65_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_65_5 (hp : 5 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 5 (transLenTr ⟨65, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 5 (transLenTr ⟨65, by decide⟩ 5 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 5 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 5 (transLenTr ⟨65, by decide⟩ 5 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_5.D1 (m := 1) from colCertDiv_147_65_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 5 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_5.D2 (m := 1) from colCertDiv_147_65_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_5_match


theorem leaf_147_65_6 (hp : 6 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 6 (transLenTr ⟨65, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 6 (transLenTr ⟨65, by decide⟩ 6 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 6 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 6 (transLenTr ⟨65, by decide⟩ 6 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_6.D1 (m := 1) from colCertDiv_147_65_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 6 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_6.D2 (m := 1) from colCertDiv_147_65_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_6_match


theorem leaf_147_65_7 (hp : 7 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 7 (transLenTr ⟨65, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 7 (transLenTr ⟨65, by decide⟩ 7 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 7 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 7 (transLenTr ⟨65, by decide⟩ 7 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_7.D1 (m := 1) from colCertDiv_147_65_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 7 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_7.D2 (m := 1) from colCertDiv_147_65_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_7_match


theorem leaf_147_65_8 (hp : 8 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 8 (transLenTr ⟨65, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 8 (transLenTr ⟨65, by decide⟩ 8 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 8 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 8 (transLenTr ⟨65, by decide⟩ 8 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_8.D1 (m := 1) from colCertDiv_147_65_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 8 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_8.D2 (m := 1) from colCertDiv_147_65_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_8_match


theorem leaf_147_65_9 (hp : 9 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 9 (transLenTr ⟨65, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 9 (transLenTr ⟨65, by decide⟩ 9 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 9 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 9 (transLenTr ⟨65, by decide⟩ 9 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_9.D1 (m := 1) from colCertDiv_147_65_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 9 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_9.D2 (m := 1) from colCertDiv_147_65_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_9_match


theorem leaf_147_65_10 (hp : 10 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 10 (transLenTr ⟨65, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 10 (transLenTr ⟨65, by decide⟩ 10 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 10 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 10 (transLenTr ⟨65, by decide⟩ 10 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_10.D1 (m := 1) from colCertDiv_147_65_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 10 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_10.D2 (m := 1) from colCertDiv_147_65_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_10_match


theorem leaf_147_65_11 (hp : 11 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 11 (transLenTr ⟨65, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 11 (transLenTr ⟨65, by decide⟩ 11 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 11 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 11 (transLenTr ⟨65, by decide⟩ 11 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_11.D1 (m := 1) from colCertDiv_147_65_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 11 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_11.D2 (m := 1) from colCertDiv_147_65_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_11_match


theorem leaf_147_65_12 (hp : 12 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 12 (transLenTr ⟨65, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 12 (transLenTr ⟨65, by decide⟩ 12 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 12 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 12 (transLenTr ⟨65, by decide⟩ 12 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_12.D1 (m := 1) from colCertDiv_147_65_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 12 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_12.D2 (m := 1) from colCertDiv_147_65_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_12_match


theorem leaf_147_65_13 (hp : 13 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 13 (transLenTr ⟨65, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 13 (transLenTr ⟨65, by decide⟩ 13 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 13 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 13 (transLenTr ⟨65, by decide⟩ 13 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_13.D1 (m := 1) from colCertDiv_147_65_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 13 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_13.D2 (m := 1) from colCertDiv_147_65_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_13_match


theorem leaf_147_65_14 (hp : 14 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 14 (transLenTr ⟨65, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 14 (transLenTr ⟨65, by decide⟩ 14 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 14 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 14 (transLenTr ⟨65, by decide⟩ 14 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_14.D1 (m := 1) from colCertDiv_147_65_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 14 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_14.D2 (m := 1) from colCertDiv_147_65_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_14_match


theorem leaf_147_65_15 (hp : 15 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 15 (transLenTr ⟨65, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 15 (transLenTr ⟨65, by decide⟩ 15 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 15 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 15 (transLenTr ⟨65, by decide⟩ 15 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_15.D1 (m := 1) from colCertDiv_147_65_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 15 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_15.D2 (m := 1) from colCertDiv_147_65_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_15_match


theorem leaf_147_65_16 (hp : 16 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 16 (transLenTr ⟨65, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 16 (transLenTr ⟨65, by decide⟩ 16 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 16 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 16 (transLenTr ⟨65, by decide⟩ 16 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_16.D1 (m := 1) from colCertDiv_147_65_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 16 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_16.D2 (m := 1) from colCertDiv_147_65_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_16_match


theorem leaf_147_65_17 (hp : 17 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 17 (transLenTr ⟨65, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 17 (transLenTr ⟨65, by decide⟩ 17 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 17 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 17 (transLenTr ⟨65, by decide⟩ 17 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_17.D1 (m := 1) from colCertDiv_147_65_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 17 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_17.D2 (m := 1) from colCertDiv_147_65_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_17_match


theorem leaf_147_65_18 (hp : 18 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 18 (transLenTr ⟨65, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 18 (transLenTr ⟨65, by decide⟩ 18 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 18 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 18 (transLenTr ⟨65, by decide⟩ 18 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_18.D1 (m := 1) from colCertDiv_147_65_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 18 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_18.D2 (m := 1) from colCertDiv_147_65_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_18_match


theorem leaf_147_65_19 (hp : 19 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 19 (transLenTr ⟨65, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 19 (transLenTr ⟨65, by decide⟩ 19 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 19 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 19 (transLenTr ⟨65, by decide⟩ 19 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_19.D1 (m := 1) from colCertDiv_147_65_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 19 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_19.D2 (m := 1) from colCertDiv_147_65_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_19_match


theorem leaf_147_65_20 (hp : 20 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 20 (transLenTr ⟨65, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 20 (transLenTr ⟨65, by decide⟩ 20 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 20 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 20 (transLenTr ⟨65, by decide⟩ 20 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_20.D1 (m := 1) from colCertDiv_147_65_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 20 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_20.D2 (m := 1) from colCertDiv_147_65_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_20_match


theorem leaf_147_65_21 (hp : 21 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 21 (transLenTr ⟨65, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 21 (transLenTr ⟨65, by decide⟩ 21 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 21 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 21 (transLenTr ⟨65, by decide⟩ 21 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_21.D1 (m := 1) from colCertDiv_147_65_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 21 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_21.D2 (m := 1) from colCertDiv_147_65_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_21_match


theorem leaf_147_65_22 (hp : 22 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 22 (transLenTr ⟨65, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 22 (transLenTr ⟨65, by decide⟩ 22 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 22 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 22 (transLenTr ⟨65, by decide⟩ 22 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_22.D1 (m := 1) from colCertDiv_147_65_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 22 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_22.D2 (m := 1) from colCertDiv_147_65_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_22_match


theorem leaf_147_65_23 (hp : 23 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 23 (transLenTr ⟨65, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 23 (transLenTr ⟨65, by decide⟩ 23 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 23 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 23 (transLenTr ⟨65, by decide⟩ 23 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_23.D1 (m := 1) from colCertDiv_147_65_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 23 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_23.D2 (m := 1) from colCertDiv_147_65_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_23_match


theorem leaf_147_65_24 (hp : 24 < (Q2.transData.getD 65 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨65, by decide⟩ : Fin 148)) (colE2 ⟨65, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨65, by decide⟩ : Fin 148))
        (colE1 ⟨65, by decide⟩ 24 (transLenTr ⟨65, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨65, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨65, by decide⟩ 24 (transLenTr ⟨65, by decide⟩ 24 hp)) T147_65
      hfix147_65 hinj147_65 hcardT147_65
      (fun i => conj_mem_of_fixedPoints _ _ (T147_65 i) (hfix147_65 i) _)
      ⟨147, by decide⟩ ⟨65, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨65, by decide⟩ 24 hp) Q2.T147_65_2 Q2.hfix147_65_2 Q2.hinj147_65_2
      Q2.hcardT147_65_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_65_2 i) (Q2.hfix147_65_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨65, by decide⟩ 24 (transLenTr ⟨65, by decide⟩ 24 hp) : ↥(reps ⟨65, by decide⟩)) : Coordinate 1)
        T147_65 = colFn colCertDiv_147_65_24.D1 (m := 1) from colCertDiv_147_65_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨65, by decide⟩ 24 hp : ↥(Q2.reps ⟨65, by decide⟩)) : Coordinate 2)
        Q2.T147_65_2 = colFn colCertDiv_147_65_24.D2 (m := 1) from colCertDiv_147_65_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_65_24_match


theorem leaf_147_66_0 (hp : 0 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 0 (transLenTr ⟨66, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 0 (transLenTr ⟨66, by decide⟩ 0 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 0 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      colCert_147_66_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_66_1 (hp : 1 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 1 (transLenTr ⟨66, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 1 (transLenTr ⟨66, by decide⟩ 1 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 1 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      colCert_147_66_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_66_2 (hp : 2 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 2 (transLenTr ⟨66, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 2 (transLenTr ⟨66, by decide⟩ 2 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 2 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      colCert_147_66_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_66_3 (hp : 3 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 3 (transLenTr ⟨66, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 3 (transLenTr ⟨66, by decide⟩ 3 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 3 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      colCert_147_66_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_66_4 (hp : 4 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 4 (transLenTr ⟨66, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 4 (transLenTr ⟨66, by decide⟩ 4 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 4 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      colCert_147_66_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_66_5 (hp : 5 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 5 (transLenTr ⟨66, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 5 (transLenTr ⟨66, by decide⟩ 5 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 5 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 5 (transLenTr ⟨66, by decide⟩ 5 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_5.D1 (m := 1) from colCertDiv_147_66_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 5 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_5.D2 (m := 1) from colCertDiv_147_66_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_5_match


theorem leaf_147_66_6 (hp : 6 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 6 (transLenTr ⟨66, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 6 (transLenTr ⟨66, by decide⟩ 6 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 6 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 6 (transLenTr ⟨66, by decide⟩ 6 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_6.D1 (m := 1) from colCertDiv_147_66_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 6 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_6.D2 (m := 1) from colCertDiv_147_66_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_6_match


theorem leaf_147_66_7 (hp : 7 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 7 (transLenTr ⟨66, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 7 (transLenTr ⟨66, by decide⟩ 7 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 7 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 7 (transLenTr ⟨66, by decide⟩ 7 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_7.D1 (m := 1) from colCertDiv_147_66_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 7 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_7.D2 (m := 1) from colCertDiv_147_66_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_7_match


theorem leaf_147_66_8 (hp : 8 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 8 (transLenTr ⟨66, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 8 (transLenTr ⟨66, by decide⟩ 8 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 8 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 8 (transLenTr ⟨66, by decide⟩ 8 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_8.D1 (m := 1) from colCertDiv_147_66_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 8 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_8.D2 (m := 1) from colCertDiv_147_66_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_8_match


theorem leaf_147_66_9 (hp : 9 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 9 (transLenTr ⟨66, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 9 (transLenTr ⟨66, by decide⟩ 9 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 9 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 9 (transLenTr ⟨66, by decide⟩ 9 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_9.D1 (m := 1) from colCertDiv_147_66_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 9 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_9.D2 (m := 1) from colCertDiv_147_66_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_9_match


theorem leaf_147_66_10 (hp : 10 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 10 (transLenTr ⟨66, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 10 (transLenTr ⟨66, by decide⟩ 10 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 10 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 10 (transLenTr ⟨66, by decide⟩ 10 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_10.D1 (m := 1) from colCertDiv_147_66_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 10 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_10.D2 (m := 1) from colCertDiv_147_66_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_10_match


theorem leaf_147_66_11 (hp : 11 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 11 (transLenTr ⟨66, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 11 (transLenTr ⟨66, by decide⟩ 11 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 11 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 11 (transLenTr ⟨66, by decide⟩ 11 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_11.D1 (m := 1) from colCertDiv_147_66_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 11 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_11.D2 (m := 1) from colCertDiv_147_66_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_11_match


theorem leaf_147_66_12 (hp : 12 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 12 (transLenTr ⟨66, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 12 (transLenTr ⟨66, by decide⟩ 12 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 12 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 12 (transLenTr ⟨66, by decide⟩ 12 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_12.D1 (m := 1) from colCertDiv_147_66_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 12 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_12.D2 (m := 1) from colCertDiv_147_66_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_12_match


theorem leaf_147_66_13 (hp : 13 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 13 (transLenTr ⟨66, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 13 (transLenTr ⟨66, by decide⟩ 13 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 13 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 13 (transLenTr ⟨66, by decide⟩ 13 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_13.D1 (m := 1) from colCertDiv_147_66_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 13 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_13.D2 (m := 1) from colCertDiv_147_66_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_13_match


theorem leaf_147_66_14 (hp : 14 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 14 (transLenTr ⟨66, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 14 (transLenTr ⟨66, by decide⟩ 14 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 14 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 14 (transLenTr ⟨66, by decide⟩ 14 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_14.D1 (m := 1) from colCertDiv_147_66_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 14 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_14.D2 (m := 1) from colCertDiv_147_66_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_14_match


theorem leaf_147_66_15 (hp : 15 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 15 (transLenTr ⟨66, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 15 (transLenTr ⟨66, by decide⟩ 15 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 15 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 15 (transLenTr ⟨66, by decide⟩ 15 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_15.D1 (m := 1) from colCertDiv_147_66_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 15 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_15.D2 (m := 1) from colCertDiv_147_66_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_15_match


theorem leaf_147_66_16 (hp : 16 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 16 (transLenTr ⟨66, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 16 (transLenTr ⟨66, by decide⟩ 16 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 16 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 16 (transLenTr ⟨66, by decide⟩ 16 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_16.D1 (m := 1) from colCertDiv_147_66_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 16 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_16.D2 (m := 1) from colCertDiv_147_66_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_16_match


theorem leaf_147_66_17 (hp : 17 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 17 (transLenTr ⟨66, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 17 (transLenTr ⟨66, by decide⟩ 17 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 17 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 17 (transLenTr ⟨66, by decide⟩ 17 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_17.D1 (m := 1) from colCertDiv_147_66_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 17 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_17.D2 (m := 1) from colCertDiv_147_66_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_17_match


theorem leaf_147_66_18 (hp : 18 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 18 (transLenTr ⟨66, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 18 (transLenTr ⟨66, by decide⟩ 18 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 18 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 18 (transLenTr ⟨66, by decide⟩ 18 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_18.D1 (m := 1) from colCertDiv_147_66_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 18 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_18.D2 (m := 1) from colCertDiv_147_66_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_18_match


theorem leaf_147_66_19 (hp : 19 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 19 (transLenTr ⟨66, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 19 (transLenTr ⟨66, by decide⟩ 19 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 19 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 19 (transLenTr ⟨66, by decide⟩ 19 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_19.D1 (m := 1) from colCertDiv_147_66_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 19 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_19.D2 (m := 1) from colCertDiv_147_66_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_19_match


theorem leaf_147_66_20 (hp : 20 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 20 (transLenTr ⟨66, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 20 (transLenTr ⟨66, by decide⟩ 20 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 20 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 20 (transLenTr ⟨66, by decide⟩ 20 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_20.D1 (m := 1) from colCertDiv_147_66_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 20 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_20.D2 (m := 1) from colCertDiv_147_66_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_20_match


theorem leaf_147_66_21 (hp : 21 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 21 (transLenTr ⟨66, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 21 (transLenTr ⟨66, by decide⟩ 21 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 21 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 21 (transLenTr ⟨66, by decide⟩ 21 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_21.D1 (m := 1) from colCertDiv_147_66_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 21 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_21.D2 (m := 1) from colCertDiv_147_66_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_21_match


theorem leaf_147_66_22 (hp : 22 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 22 (transLenTr ⟨66, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 22 (transLenTr ⟨66, by decide⟩ 22 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 22 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 22 (transLenTr ⟨66, by decide⟩ 22 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_22.D1 (m := 1) from colCertDiv_147_66_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 22 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_22.D2 (m := 1) from colCertDiv_147_66_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_22_match


theorem leaf_147_66_23 (hp : 23 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 23 (transLenTr ⟨66, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 23 (transLenTr ⟨66, by decide⟩ 23 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 23 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 23 (transLenTr ⟨66, by decide⟩ 23 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_23.D1 (m := 1) from colCertDiv_147_66_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 23 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_23.D2 (m := 1) from colCertDiv_147_66_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_23_match


theorem leaf_147_66_24 (hp : 24 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 24 (transLenTr ⟨66, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 24 (transLenTr ⟨66, by decide⟩ 24 hp)) T147_66
      hfix147_66 hinj147_66 hcardT147_66
      (fun i => conj_mem_of_fixedPoints _ _ (T147_66 i) (hfix147_66 i) _)
      ⟨147, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 24 hp) Q2.T147_66_2 Q2.hfix147_66_2 Q2.hinj147_66_2
      Q2.hcardT147_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_66_2 i) (Q2.hfix147_66_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨66, by decide⟩ 24 (transLenTr ⟨66, by decide⟩ 24 hp) : ↥(reps ⟨66, by decide⟩)) : Coordinate 1)
        T147_66 = colFn colCertDiv_147_66_24.D1 (m := 1) from colCertDiv_147_66_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨66, by decide⟩ 24 hp : ↥(Q2.reps ⟨66, by decide⟩)) : Coordinate 2)
        Q2.T147_66_2 = colFn colCertDiv_147_66_24.D2 (m := 1) from colCertDiv_147_66_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_66_24_match


theorem leaf_147_67_0 (hp : 0 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 0 (transLenTr ⟨67, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 0 (transLenTr ⟨67, by decide⟩ 0 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 0 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_1 (hp : 1 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 1 (transLenTr ⟨67, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 1 (transLenTr ⟨67, by decide⟩ 1 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 1 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_2 (hp : 2 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 2 (transLenTr ⟨67, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 2 (transLenTr ⟨67, by decide⟩ 2 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 2 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_3 (hp : 3 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 3 (transLenTr ⟨67, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 3 (transLenTr ⟨67, by decide⟩ 3 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 3 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_4 (hp : 4 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 4 (transLenTr ⟨67, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 4 (transLenTr ⟨67, by decide⟩ 4 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 4 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_5 (hp : 5 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 5 (transLenTr ⟨67, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 5 (transLenTr ⟨67, by decide⟩ 5 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 5 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_6 (hp : 6 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 6 (transLenTr ⟨67, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 6 (transLenTr ⟨67, by decide⟩ 6 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 6 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_7 (hp : 7 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 7 (transLenTr ⟨67, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 7 (transLenTr ⟨67, by decide⟩ 7 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 7 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_8 (hp : 8 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 8 (transLenTr ⟨67, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 8 (transLenTr ⟨67, by decide⟩ 8 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 8 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_9 (hp : 9 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 9 (transLenTr ⟨67, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 9 (transLenTr ⟨67, by decide⟩ 9 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 9 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_10 (hp : 10 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 10 (transLenTr ⟨67, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 10 (transLenTr ⟨67, by decide⟩ 10 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 10 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_11 (hp : 11 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 11 (transLenTr ⟨67, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 11 (transLenTr ⟨67, by decide⟩ 11 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 11 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_12 (hp : 12 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 12 (transLenTr ⟨67, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 12 (transLenTr ⟨67, by decide⟩ 12 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 12 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_13 (hp : 13 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 13 (transLenTr ⟨67, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 13 (transLenTr ⟨67, by decide⟩ 13 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 13 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_14 (hp : 14 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 14 (transLenTr ⟨67, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 14 (transLenTr ⟨67, by decide⟩ 14 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 14 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_15 (hp : 15 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 15 (transLenTr ⟨67, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 15 (transLenTr ⟨67, by decide⟩ 15 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 15 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_16 (hp : 16 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 16 (transLenTr ⟨67, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 16 (transLenTr ⟨67, by decide⟩ 16 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 16 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_17 (hp : 17 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 17 (transLenTr ⟨67, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 17 (transLenTr ⟨67, by decide⟩ 17 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 17 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_18 (hp : 18 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 18 (transLenTr ⟨67, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 18 (transLenTr ⟨67, by decide⟩ 18 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 18 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_19 (hp : 19 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 19 (transLenTr ⟨67, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 19 (transLenTr ⟨67, by decide⟩ 19 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 19 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_20 (hp : 20 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 20 (transLenTr ⟨67, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 20 (transLenTr ⟨67, by decide⟩ 20 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 20 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_21 (hp : 21 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 21 (transLenTr ⟨67, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 21 (transLenTr ⟨67, by decide⟩ 21 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 21 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_22 (hp : 22 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 22 (transLenTr ⟨67, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 22 (transLenTr ⟨67, by decide⟩ 22 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 22 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_23 (hp : 23 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 23 (transLenTr ⟨67, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 23 (transLenTr ⟨67, by decide⟩ 23 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 23 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_24 (hp : 24 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 24 (transLenTr ⟨67, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 24 (transLenTr ⟨67, by decide⟩ 24 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 24 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_25 (hp : 25 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 25 (transLenTr ⟨67, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 25 (transLenTr ⟨67, by decide⟩ 25 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 25 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_30 (hp : 30 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 30 (transLenTr ⟨67, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 30 (transLenTr ⟨67, by decide⟩ 30 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 30 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_35 (hp : 35 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 35 (transLenTr ⟨67, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 35 (transLenTr ⟨67, by decide⟩ 35 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 35 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_40 (hp : 40 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 40 (transLenTr ⟨67, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 40 (transLenTr ⟨67, by decide⟩ 40 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 40 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_45 (hp : 45 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 45 (transLenTr ⟨67, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 45 (transLenTr ⟨67, by decide⟩ 45 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 45 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_50 (hp : 50 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 50 (transLenTr ⟨67, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 50 (transLenTr ⟨67, by decide⟩ 50 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 50 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_55 (hp : 55 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 55 (transLenTr ⟨67, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 55 (transLenTr ⟨67, by decide⟩ 55 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 55 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_55.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_60 (hp : 60 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 60 (transLenTr ⟨67, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 60 (transLenTr ⟨67, by decide⟩ 60 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 60 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_60.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_65 (hp : 65 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 65 (transLenTr ⟨67, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 65 (transLenTr ⟨67, by decide⟩ 65 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 65 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_65.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_70 (hp : 70 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 70 (transLenTr ⟨67, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 70 (transLenTr ⟨67, by decide⟩ 70 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 70 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      colCert_147_67_70.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_67_75 (hp : 75 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 75 (transLenTr ⟨67, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 75 (transLenTr ⟨67, by decide⟩ 75 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 75 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 75 (transLenTr ⟨67, by decide⟩ 75 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T147_67 = colFn colCertDiv_147_67_75.D1 (m := 1) from colCertDiv_147_67_75.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 75 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T147_67_2 = colFn colCertDiv_147_67_75.D2 (m := 1) from colCertDiv_147_67_75.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_67_75_match


theorem leaf_147_67_80 (hp : 80 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 80 (transLenTr ⟨67, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 80 (transLenTr ⟨67, by decide⟩ 80 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 80 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 80 (transLenTr ⟨67, by decide⟩ 80 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T147_67 = colFn colCertDiv_147_67_80.D1 (m := 1) from colCertDiv_147_67_80.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 80 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T147_67_2 = colFn colCertDiv_147_67_80.D2 (m := 1) from colCertDiv_147_67_80.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_67_80_match


theorem leaf_147_67_85 (hp : 85 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 85 (transLenTr ⟨67, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 85 (transLenTr ⟨67, by decide⟩ 85 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 85 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 85 (transLenTr ⟨67, by decide⟩ 85 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T147_67 = colFn colCertDiv_147_67_85.D1 (m := 1) from colCertDiv_147_67_85.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 85 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T147_67_2 = colFn colCertDiv_147_67_85.D2 (m := 1) from colCertDiv_147_67_85.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_67_85_match


theorem leaf_147_67_90 (hp : 90 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 90 (transLenTr ⟨67, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 90 (transLenTr ⟨67, by decide⟩ 90 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 90 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 90 (transLenTr ⟨67, by decide⟩ 90 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T147_67 = colFn colCertDiv_147_67_90.D1 (m := 1) from colCertDiv_147_67_90.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 90 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T147_67_2 = colFn colCertDiv_147_67_90.D2 (m := 1) from colCertDiv_147_67_90.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_67_90_match


theorem leaf_147_67_95 (hp : 95 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 95 (transLenTr ⟨67, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 95 (transLenTr ⟨67, by decide⟩ 95 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 95 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 95 (transLenTr ⟨67, by decide⟩ 95 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T147_67 = colFn colCertDiv_147_67_95.D1 (m := 1) from colCertDiv_147_67_95.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 95 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T147_67_2 = colFn colCertDiv_147_67_95.D2 (m := 1) from colCertDiv_147_67_95.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_67_95_match


theorem leaf_147_67_100 (hp : 100 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 100 (transLenTr ⟨67, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 100 (transLenTr ⟨67, by decide⟩ 100 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 100 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 100 (transLenTr ⟨67, by decide⟩ 100 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T147_67 = colFn colCertDiv_147_67_100.D1 (m := 1) from colCertDiv_147_67_100.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 100 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T147_67_2 = colFn colCertDiv_147_67_100.D2 (m := 1) from colCertDiv_147_67_100.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_67_100_match


theorem leaf_147_67_105 (hp : 105 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 105 (transLenTr ⟨67, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 105 (transLenTr ⟨67, by decide⟩ 105 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 105 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 105 (transLenTr ⟨67, by decide⟩ 105 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T147_67 = colFn colCertDiv_147_67_105.D1 (m := 1) from colCertDiv_147_67_105.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 105 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T147_67_2 = colFn colCertDiv_147_67_105.D2 (m := 1) from colCertDiv_147_67_105.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_67_105_match


theorem leaf_147_67_110 (hp : 110 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 110 (transLenTr ⟨67, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 110 (transLenTr ⟨67, by decide⟩ 110 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 110 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 110 (transLenTr ⟨67, by decide⟩ 110 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T147_67 = colFn colCertDiv_147_67_110.D1 (m := 1) from colCertDiv_147_67_110.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 110 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T147_67_2 = colFn colCertDiv_147_67_110.D2 (m := 1) from colCertDiv_147_67_110.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_67_110_match


theorem leaf_147_67_115 (hp : 115 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 115 (transLenTr ⟨67, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 115 (transLenTr ⟨67, by decide⟩ 115 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 115 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 115 (transLenTr ⟨67, by decide⟩ 115 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T147_67 = colFn colCertDiv_147_67_115.D1 (m := 1) from colCertDiv_147_67_115.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 115 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T147_67_2 = colFn colCertDiv_147_67_115.D2 (m := 1) from colCertDiv_147_67_115.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_67_115_match


theorem leaf_147_67_120 (hp : 120 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 120 (transLenTr ⟨67, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 120 (transLenTr ⟨67, by decide⟩ 120 hp)) T147_67
      hfix147_67 hinj147_67 hcardT147_67
      (fun i => conj_mem_of_fixedPoints _ _ (T147_67 i) (hfix147_67 i) _)
      ⟨147, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 120 hp) Q2.T147_67_2 Q2.hfix147_67_2 Q2.hinj147_67_2
      Q2.hcardT147_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_67_2 i) (Q2.hfix147_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 120 (transLenTr ⟨67, by decide⟩ 120 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T147_67 = colFn colCertDiv_147_67_120.D1 (m := 1) from colCertDiv_147_67_120.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 120 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T147_67_2 = colFn colCertDiv_147_67_120.D2 (m := 1) from colCertDiv_147_67_120.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_67_120_match


theorem leaf_147_68_0 (hp : 0 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 0 (transLenTr ⟨68, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 0 (transLenTr ⟨68, by decide⟩ 0 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 0 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      colCert_147_68_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_68_1 (hp : 1 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 1 (transLenTr ⟨68, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 1 (transLenTr ⟨68, by decide⟩ 1 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 1 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      colCert_147_68_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_68_2 (hp : 2 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 2 (transLenTr ⟨68, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 2 (transLenTr ⟨68, by decide⟩ 2 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 2 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      colCert_147_68_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_68_3 (hp : 3 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 3 (transLenTr ⟨68, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 3 (transLenTr ⟨68, by decide⟩ 3 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 3 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      colCert_147_68_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_68_4 (hp : 4 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 4 (transLenTr ⟨68, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 4 (transLenTr ⟨68, by decide⟩ 4 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 4 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      colCert_147_68_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_68_5 (hp : 5 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 5 (transLenTr ⟨68, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 5 (transLenTr ⟨68, by decide⟩ 5 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 5 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 5 (transLenTr ⟨68, by decide⟩ 5 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_5.D1 (m := 1) from colCertDiv_147_68_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 5 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_5.D2 (m := 1) from colCertDiv_147_68_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_5_match


theorem leaf_147_68_6 (hp : 6 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 6 (transLenTr ⟨68, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 6 (transLenTr ⟨68, by decide⟩ 6 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 6 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 6 (transLenTr ⟨68, by decide⟩ 6 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_6.D1 (m := 1) from colCertDiv_147_68_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 6 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_6.D2 (m := 1) from colCertDiv_147_68_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_6_match


theorem leaf_147_68_7 (hp : 7 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 7 (transLenTr ⟨68, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 7 (transLenTr ⟨68, by decide⟩ 7 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 7 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 7 (transLenTr ⟨68, by decide⟩ 7 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_7.D1 (m := 1) from colCertDiv_147_68_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 7 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_7.D2 (m := 1) from colCertDiv_147_68_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_7_match


theorem leaf_147_68_8 (hp : 8 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 8 (transLenTr ⟨68, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 8 (transLenTr ⟨68, by decide⟩ 8 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 8 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 8 (transLenTr ⟨68, by decide⟩ 8 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_8.D1 (m := 1) from colCertDiv_147_68_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 8 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_8.D2 (m := 1) from colCertDiv_147_68_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_8_match


theorem leaf_147_68_9 (hp : 9 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 9 (transLenTr ⟨68, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 9 (transLenTr ⟨68, by decide⟩ 9 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 9 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 9 (transLenTr ⟨68, by decide⟩ 9 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_9.D1 (m := 1) from colCertDiv_147_68_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 9 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_9.D2 (m := 1) from colCertDiv_147_68_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_9_match


theorem leaf_147_68_10 (hp : 10 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 10 (transLenTr ⟨68, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 10 (transLenTr ⟨68, by decide⟩ 10 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 10 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 10 (transLenTr ⟨68, by decide⟩ 10 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_10.D1 (m := 1) from colCertDiv_147_68_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 10 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_10.D2 (m := 1) from colCertDiv_147_68_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_10_match


theorem leaf_147_68_11 (hp : 11 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 11 (transLenTr ⟨68, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 11 (transLenTr ⟨68, by decide⟩ 11 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 11 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 11 (transLenTr ⟨68, by decide⟩ 11 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_11.D1 (m := 1) from colCertDiv_147_68_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 11 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_11.D2 (m := 1) from colCertDiv_147_68_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_11_match


theorem leaf_147_68_12 (hp : 12 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 12 (transLenTr ⟨68, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 12 (transLenTr ⟨68, by decide⟩ 12 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 12 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 12 (transLenTr ⟨68, by decide⟩ 12 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_12.D1 (m := 1) from colCertDiv_147_68_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 12 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_12.D2 (m := 1) from colCertDiv_147_68_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_12_match


theorem leaf_147_68_13 (hp : 13 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 13 (transLenTr ⟨68, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 13 (transLenTr ⟨68, by decide⟩ 13 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 13 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 13 (transLenTr ⟨68, by decide⟩ 13 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_13.D1 (m := 1) from colCertDiv_147_68_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 13 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_13.D2 (m := 1) from colCertDiv_147_68_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_13_match


theorem leaf_147_68_14 (hp : 14 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 14 (transLenTr ⟨68, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 14 (transLenTr ⟨68, by decide⟩ 14 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 14 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 14 (transLenTr ⟨68, by decide⟩ 14 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_14.D1 (m := 1) from colCertDiv_147_68_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 14 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_14.D2 (m := 1) from colCertDiv_147_68_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_14_match


theorem leaf_147_68_15 (hp : 15 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 15 (transLenTr ⟨68, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 15 (transLenTr ⟨68, by decide⟩ 15 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 15 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 15 (transLenTr ⟨68, by decide⟩ 15 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_15.D1 (m := 1) from colCertDiv_147_68_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 15 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_15.D2 (m := 1) from colCertDiv_147_68_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_15_match


theorem leaf_147_68_16 (hp : 16 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 16 (transLenTr ⟨68, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 16 (transLenTr ⟨68, by decide⟩ 16 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 16 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 16 (transLenTr ⟨68, by decide⟩ 16 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_16.D1 (m := 1) from colCertDiv_147_68_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 16 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_16.D2 (m := 1) from colCertDiv_147_68_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_16_match


theorem leaf_147_68_17 (hp : 17 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 17 (transLenTr ⟨68, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 17 (transLenTr ⟨68, by decide⟩ 17 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 17 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 17 (transLenTr ⟨68, by decide⟩ 17 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_17.D1 (m := 1) from colCertDiv_147_68_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 17 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_17.D2 (m := 1) from colCertDiv_147_68_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_17_match


theorem leaf_147_68_18 (hp : 18 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 18 (transLenTr ⟨68, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 18 (transLenTr ⟨68, by decide⟩ 18 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 18 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 18 (transLenTr ⟨68, by decide⟩ 18 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_18.D1 (m := 1) from colCertDiv_147_68_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 18 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_18.D2 (m := 1) from colCertDiv_147_68_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_18_match


theorem leaf_147_68_19 (hp : 19 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 19 (transLenTr ⟨68, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 19 (transLenTr ⟨68, by decide⟩ 19 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 19 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 19 (transLenTr ⟨68, by decide⟩ 19 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_19.D1 (m := 1) from colCertDiv_147_68_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 19 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_19.D2 (m := 1) from colCertDiv_147_68_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_19_tau_match


theorem leaf_147_68_20 (hp : 20 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 20 (transLenTr ⟨68, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 20 (transLenTr ⟨68, by decide⟩ 20 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 20 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 20 (transLenTr ⟨68, by decide⟩ 20 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_20.D1 (m := 1) from colCertDiv_147_68_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 20 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_20.D2 (m := 1) from colCertDiv_147_68_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_20_tau_match


theorem leaf_147_68_21 (hp : 21 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 21 (transLenTr ⟨68, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 21 (transLenTr ⟨68, by decide⟩ 21 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 21 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 21 (transLenTr ⟨68, by decide⟩ 21 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_21.D1 (m := 1) from colCertDiv_147_68_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 21 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_21.D2 (m := 1) from colCertDiv_147_68_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_21_tau_match


theorem leaf_147_68_22 (hp : 22 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 22 (transLenTr ⟨68, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 22 (transLenTr ⟨68, by decide⟩ 22 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 22 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 22 (transLenTr ⟨68, by decide⟩ 22 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_22.D1 (m := 1) from colCertDiv_147_68_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 22 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_22.D2 (m := 1) from colCertDiv_147_68_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_22_tau_match


theorem leaf_147_68_23 (hp : 23 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 23 (transLenTr ⟨68, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 23 (transLenTr ⟨68, by decide⟩ 23 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 23 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 23 (transLenTr ⟨68, by decide⟩ 23 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_23.D1 (m := 1) from colCertDiv_147_68_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 23 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_23.D2 (m := 1) from colCertDiv_147_68_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_23_match


theorem leaf_147_68_24 (hp : 24 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 24 (transLenTr ⟨68, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 24 (transLenTr ⟨68, by decide⟩ 24 hp)) T147_68
      hfix147_68 hinj147_68 hcardT147_68
      (fun i => conj_mem_of_fixedPoints _ _ (T147_68 i) (hfix147_68 i) _)
      ⟨147, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 24 hp) Q2.T147_68_2 Q2.hfix147_68_2 Q2.hinj147_68_2
      Q2.hcardT147_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_68_2 i) (Q2.hfix147_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 24 (transLenTr ⟨68, by decide⟩ 24 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T147_68 = colFn colCertDiv_147_68_24.D1 (m := 1) from colCertDiv_147_68_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 24 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T147_68_2 = colFn colCertDiv_147_68_24.D2 (m := 1) from colCertDiv_147_68_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_68_24_match


theorem leaf_147_69_0 (hp : 0 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 0 (transLenTr ⟨69, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 0 (transLenTr ⟨69, by decide⟩ 0 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 0 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_1 (hp : 1 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 1 (transLenTr ⟨69, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 1 (transLenTr ⟨69, by decide⟩ 1 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 1 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_2 (hp : 2 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 2 (transLenTr ⟨69, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 2 (transLenTr ⟨69, by decide⟩ 2 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 2 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_3 (hp : 3 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 3 (transLenTr ⟨69, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 3 (transLenTr ⟨69, by decide⟩ 3 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 3 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_4 (hp : 4 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 4 (transLenTr ⟨69, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 4 (transLenTr ⟨69, by decide⟩ 4 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 4 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_5 (hp : 5 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 5 (transLenTr ⟨69, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 5 (transLenTr ⟨69, by decide⟩ 5 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 5 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_6 (hp : 6 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 6 (transLenTr ⟨69, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 6 (transLenTr ⟨69, by decide⟩ 6 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 6 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_7 (hp : 7 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 7 (transLenTr ⟨69, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 7 (transLenTr ⟨69, by decide⟩ 7 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 7 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_8 (hp : 8 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 8 (transLenTr ⟨69, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 8 (transLenTr ⟨69, by decide⟩ 8 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 8 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_9 (hp : 9 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 9 (transLenTr ⟨69, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 9 (transLenTr ⟨69, by decide⟩ 9 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 9 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_10 (hp : 10 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 10 (transLenTr ⟨69, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 10 (transLenTr ⟨69, by decide⟩ 10 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 10 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_11 (hp : 11 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 11 (transLenTr ⟨69, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 11 (transLenTr ⟨69, by decide⟩ 11 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 11 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_12 (hp : 12 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 12 (transLenTr ⟨69, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 12 (transLenTr ⟨69, by decide⟩ 12 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 12 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_13 (hp : 13 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 13 (transLenTr ⟨69, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 13 (transLenTr ⟨69, by decide⟩ 13 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 13 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_14 (hp : 14 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 14 (transLenTr ⟨69, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 14 (transLenTr ⟨69, by decide⟩ 14 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 14 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      colCert_147_69_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_69_15 (hp : 15 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 15 (transLenTr ⟨69, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 15 (transLenTr ⟨69, by decide⟩ 15 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 15 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨69, by decide⟩ 15 (transLenTr ⟨69, by decide⟩ 15 hp) : ↥(reps ⟨69, by decide⟩)) : Coordinate 1)
        T147_69 = colFn colCertDiv_147_69_15.D1 (m := 1) from colCertDiv_147_69_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨69, by decide⟩ 15 hp : ↥(Q2.reps ⟨69, by decide⟩)) : Coordinate 2)
        Q2.T147_69_2 = colFn colCertDiv_147_69_15.D2 (m := 1) from colCertDiv_147_69_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_69_15_match


theorem leaf_147_69_16 (hp : 16 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 16 (transLenTr ⟨69, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 16 (transLenTr ⟨69, by decide⟩ 16 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 16 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨69, by decide⟩ 16 (transLenTr ⟨69, by decide⟩ 16 hp) : ↥(reps ⟨69, by decide⟩)) : Coordinate 1)
        T147_69 = colFn colCertDiv_147_69_16.D1 (m := 1) from colCertDiv_147_69_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨69, by decide⟩ 16 hp : ↥(Q2.reps ⟨69, by decide⟩)) : Coordinate 2)
        Q2.T147_69_2 = colFn colCertDiv_147_69_16.D2 (m := 1) from colCertDiv_147_69_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_69_16_match


theorem leaf_147_69_17 (hp : 17 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 17 (transLenTr ⟨69, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 17 (transLenTr ⟨69, by decide⟩ 17 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 17 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨69, by decide⟩ 17 (transLenTr ⟨69, by decide⟩ 17 hp) : ↥(reps ⟨69, by decide⟩)) : Coordinate 1)
        T147_69 = colFn colCertDiv_147_69_17.D1 (m := 1) from colCertDiv_147_69_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨69, by decide⟩ 17 hp : ↥(Q2.reps ⟨69, by decide⟩)) : Coordinate 2)
        Q2.T147_69_2 = colFn colCertDiv_147_69_17.D2 (m := 1) from colCertDiv_147_69_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_69_17_match


theorem leaf_147_69_18 (hp : 18 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 18 (transLenTr ⟨69, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 18 (transLenTr ⟨69, by decide⟩ 18 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 18 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨69, by decide⟩ 18 (transLenTr ⟨69, by decide⟩ 18 hp) : ↥(reps ⟨69, by decide⟩)) : Coordinate 1)
        T147_69 = colFn colCertDiv_147_69_18.D1 (m := 1) from colCertDiv_147_69_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨69, by decide⟩ 18 hp : ↥(Q2.reps ⟨69, by decide⟩)) : Coordinate 2)
        Q2.T147_69_2 = colFn colCertDiv_147_69_18.D2 (m := 1) from colCertDiv_147_69_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_69_18_match


theorem leaf_147_69_19 (hp : 19 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 19 (transLenTr ⟨69, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 19 (transLenTr ⟨69, by decide⟩ 19 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 19 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨69, by decide⟩ 19 (transLenTr ⟨69, by decide⟩ 19 hp) : ↥(reps ⟨69, by decide⟩)) : Coordinate 1)
        T147_69 = colFn colCertDiv_147_69_19.D1 (m := 1) from colCertDiv_147_69_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨69, by decide⟩ 19 hp : ↥(Q2.reps ⟨69, by decide⟩)) : Coordinate 2)
        Q2.T147_69_2 = colFn colCertDiv_147_69_19.D2 (m := 1) from colCertDiv_147_69_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_69_19_match


theorem leaf_147_69_20 (hp : 20 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 20 (transLenTr ⟨69, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 20 (transLenTr ⟨69, by decide⟩ 20 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 20 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨69, by decide⟩ 20 (transLenTr ⟨69, by decide⟩ 20 hp) : ↥(reps ⟨69, by decide⟩)) : Coordinate 1)
        T147_69 = colFn colCertDiv_147_69_20.D1 (m := 1) from colCertDiv_147_69_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨69, by decide⟩ 20 hp : ↥(Q2.reps ⟨69, by decide⟩)) : Coordinate 2)
        Q2.T147_69_2 = colFn colCertDiv_147_69_20.D2 (m := 1) from colCertDiv_147_69_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_69_20_match


theorem leaf_147_69_21 (hp : 21 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 21 (transLenTr ⟨69, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 21 (transLenTr ⟨69, by decide⟩ 21 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 21 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨69, by decide⟩ 21 (transLenTr ⟨69, by decide⟩ 21 hp) : ↥(reps ⟨69, by decide⟩)) : Coordinate 1)
        T147_69 = colFn colCertDiv_147_69_21.D1 (m := 1) from colCertDiv_147_69_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨69, by decide⟩ 21 hp : ↥(Q2.reps ⟨69, by decide⟩)) : Coordinate 2)
        Q2.T147_69_2 = colFn colCertDiv_147_69_21.D2 (m := 1) from colCertDiv_147_69_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_69_21_match


theorem leaf_147_69_22 (hp : 22 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 22 (transLenTr ⟨69, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 22 (transLenTr ⟨69, by decide⟩ 22 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 22 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨69, by decide⟩ 22 (transLenTr ⟨69, by decide⟩ 22 hp) : ↥(reps ⟨69, by decide⟩)) : Coordinate 1)
        T147_69 = colFn colCertDiv_147_69_22.D1 (m := 1) from colCertDiv_147_69_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨69, by decide⟩ 22 hp : ↥(Q2.reps ⟨69, by decide⟩)) : Coordinate 2)
        Q2.T147_69_2 = colFn colCertDiv_147_69_22.D2 (m := 1) from colCertDiv_147_69_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_69_22_match


theorem leaf_147_69_23 (hp : 23 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 23 (transLenTr ⟨69, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 23 (transLenTr ⟨69, by decide⟩ 23 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 23 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨69, by decide⟩ 23 (transLenTr ⟨69, by decide⟩ 23 hp) : ↥(reps ⟨69, by decide⟩)) : Coordinate 1)
        T147_69 = colFn colCertDiv_147_69_23.D1 (m := 1) from colCertDiv_147_69_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨69, by decide⟩ 23 hp : ↥(Q2.reps ⟨69, by decide⟩)) : Coordinate 2)
        Q2.T147_69_2 = colFn colCertDiv_147_69_23.D2 (m := 1) from colCertDiv_147_69_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_69_23_match


theorem leaf_147_69_24 (hp : 24 < (Q2.transData.getD 69 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ 24 (transLenTr ⟨69, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨69, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨69, by decide⟩ 24 (transLenTr ⟨69, by decide⟩ 24 hp)) T147_69
      hfix147_69 hinj147_69 hcardT147_69
      (fun i => conj_mem_of_fixedPoints _ _ (T147_69 i) (hfix147_69 i) _)
      ⟨147, by decide⟩ ⟨69, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨69, by decide⟩ 24 hp) Q2.T147_69_2 Q2.hfix147_69_2 Q2.hinj147_69_2
      Q2.hcardT147_69_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_69_2 i) (Q2.hfix147_69_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨69, by decide⟩ 24 (transLenTr ⟨69, by decide⟩ 24 hp) : ↥(reps ⟨69, by decide⟩)) : Coordinate 1)
        T147_69 = colFn colCertDiv_147_69_24.D1 (m := 1) from colCertDiv_147_69_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨69, by decide⟩ 24 hp : ↥(Q2.reps ⟨69, by decide⟩)) : Coordinate 2)
        Q2.T147_69_2 = colFn colCertDiv_147_69_24.D2 (m := 1) from colCertDiv_147_69_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_69_24_match


theorem leaf_147_70_0 (hp : 0 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 0 (transLenTr ⟨70, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 0 (transLenTr ⟨70, by decide⟩ 0 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 0 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      colCert_147_70_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_70_1 (hp : 1 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 1 (transLenTr ⟨70, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 1 (transLenTr ⟨70, by decide⟩ 1 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 1 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      colCert_147_70_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_70_2 (hp : 2 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 2 (transLenTr ⟨70, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 2 (transLenTr ⟨70, by decide⟩ 2 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 2 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      colCert_147_70_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_70_3 (hp : 3 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 3 (transLenTr ⟨70, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 3 (transLenTr ⟨70, by decide⟩ 3 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 3 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      colCert_147_70_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_70_4 (hp : 4 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 4 (transLenTr ⟨70, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 4 (transLenTr ⟨70, by decide⟩ 4 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 4 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      colCert_147_70_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_70_5 (hp : 5 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 5 (transLenTr ⟨70, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 5 (transLenTr ⟨70, by decide⟩ 5 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 5 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 5 (transLenTr ⟨70, by decide⟩ 5 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_5.D1 (m := 1) from colCertDiv_147_70_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 5 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_5.D2 (m := 1) from colCertDiv_147_70_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_5_match


theorem leaf_147_70_6 (hp : 6 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 6 (transLenTr ⟨70, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 6 (transLenTr ⟨70, by decide⟩ 6 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 6 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 6 (transLenTr ⟨70, by decide⟩ 6 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_6.D1 (m := 1) from colCertDiv_147_70_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 6 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_6.D2 (m := 1) from colCertDiv_147_70_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_6_match


theorem leaf_147_70_7 (hp : 7 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 7 (transLenTr ⟨70, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 7 (transLenTr ⟨70, by decide⟩ 7 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 7 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 7 (transLenTr ⟨70, by decide⟩ 7 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_7.D1 (m := 1) from colCertDiv_147_70_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 7 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_7.D2 (m := 1) from colCertDiv_147_70_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_7_match


theorem leaf_147_70_8 (hp : 8 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 8 (transLenTr ⟨70, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 8 (transLenTr ⟨70, by decide⟩ 8 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 8 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 8 (transLenTr ⟨70, by decide⟩ 8 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_8.D1 (m := 1) from colCertDiv_147_70_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 8 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_8.D2 (m := 1) from colCertDiv_147_70_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_8_match


theorem leaf_147_70_9 (hp : 9 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 9 (transLenTr ⟨70, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 9 (transLenTr ⟨70, by decide⟩ 9 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 9 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 9 (transLenTr ⟨70, by decide⟩ 9 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_9.D1 (m := 1) from colCertDiv_147_70_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 9 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_9.D2 (m := 1) from colCertDiv_147_70_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_9_match


theorem leaf_147_70_10 (hp : 10 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 10 (transLenTr ⟨70, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 10 (transLenTr ⟨70, by decide⟩ 10 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 10 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 10 (transLenTr ⟨70, by decide⟩ 10 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_10.D1 (m := 1) from colCertDiv_147_70_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 10 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_10.D2 (m := 1) from colCertDiv_147_70_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_10_match


theorem leaf_147_70_11 (hp : 11 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 11 (transLenTr ⟨70, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 11 (transLenTr ⟨70, by decide⟩ 11 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 11 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 11 (transLenTr ⟨70, by decide⟩ 11 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_11.D1 (m := 1) from colCertDiv_147_70_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 11 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_11.D2 (m := 1) from colCertDiv_147_70_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_11_match


theorem leaf_147_70_12 (hp : 12 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 12 (transLenTr ⟨70, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 12 (transLenTr ⟨70, by decide⟩ 12 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 12 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 12 (transLenTr ⟨70, by decide⟩ 12 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_12.D1 (m := 1) from colCertDiv_147_70_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 12 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_12.D2 (m := 1) from colCertDiv_147_70_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_12_match


theorem leaf_147_70_13 (hp : 13 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 13 (transLenTr ⟨70, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 13 (transLenTr ⟨70, by decide⟩ 13 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 13 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 13 (transLenTr ⟨70, by decide⟩ 13 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_13.D1 (m := 1) from colCertDiv_147_70_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 13 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_13.D2 (m := 1) from colCertDiv_147_70_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_13_match


theorem leaf_147_70_14 (hp : 14 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 14 (transLenTr ⟨70, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 14 (transLenTr ⟨70, by decide⟩ 14 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 14 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 14 (transLenTr ⟨70, by decide⟩ 14 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_14.D1 (m := 1) from colCertDiv_147_70_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 14 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_14.D2 (m := 1) from colCertDiv_147_70_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_14_match


theorem leaf_147_70_15 (hp : 15 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 15 (transLenTr ⟨70, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 15 (transLenTr ⟨70, by decide⟩ 15 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 15 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 15 (transLenTr ⟨70, by decide⟩ 15 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_15.D1 (m := 1) from colCertDiv_147_70_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 15 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_15.D2 (m := 1) from colCertDiv_147_70_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_15_match


theorem leaf_147_70_16 (hp : 16 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 16 (transLenTr ⟨70, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 16 (transLenTr ⟨70, by decide⟩ 16 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 16 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 16 (transLenTr ⟨70, by decide⟩ 16 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_16.D1 (m := 1) from colCertDiv_147_70_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 16 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_16.D2 (m := 1) from colCertDiv_147_70_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_16_match


theorem leaf_147_70_17 (hp : 17 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 17 (transLenTr ⟨70, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 17 (transLenTr ⟨70, by decide⟩ 17 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 17 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 17 (transLenTr ⟨70, by decide⟩ 17 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_17.D1 (m := 1) from colCertDiv_147_70_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 17 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_17.D2 (m := 1) from colCertDiv_147_70_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_17_match


theorem leaf_147_70_18 (hp : 18 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 18 (transLenTr ⟨70, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 18 (transLenTr ⟨70, by decide⟩ 18 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 18 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 18 (transLenTr ⟨70, by decide⟩ 18 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_18.D1 (m := 1) from colCertDiv_147_70_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 18 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_18.D2 (m := 1) from colCertDiv_147_70_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_18_match


theorem leaf_147_70_19 (hp : 19 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 19 (transLenTr ⟨70, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 19 (transLenTr ⟨70, by decide⟩ 19 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 19 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 19 (transLenTr ⟨70, by decide⟩ 19 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_19.D1 (m := 1) from colCertDiv_147_70_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 19 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_19.D2 (m := 1) from colCertDiv_147_70_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_19_match


theorem leaf_147_70_20 (hp : 20 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 20 (transLenTr ⟨70, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 20 (transLenTr ⟨70, by decide⟩ 20 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 20 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 20 (transLenTr ⟨70, by decide⟩ 20 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_20.D1 (m := 1) from colCertDiv_147_70_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 20 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_20.D2 (m := 1) from colCertDiv_147_70_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_20_match


theorem leaf_147_70_21 (hp : 21 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 21 (transLenTr ⟨70, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 21 (transLenTr ⟨70, by decide⟩ 21 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 21 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 21 (transLenTr ⟨70, by decide⟩ 21 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_21.D1 (m := 1) from colCertDiv_147_70_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 21 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_21.D2 (m := 1) from colCertDiv_147_70_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_21_match


theorem leaf_147_70_22 (hp : 22 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 22 (transLenTr ⟨70, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 22 (transLenTr ⟨70, by decide⟩ 22 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 22 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 22 (transLenTr ⟨70, by decide⟩ 22 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_22.D1 (m := 1) from colCertDiv_147_70_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 22 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_22.D2 (m := 1) from colCertDiv_147_70_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_22_match


theorem leaf_147_70_23 (hp : 23 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 23 (transLenTr ⟨70, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 23 (transLenTr ⟨70, by decide⟩ 23 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 23 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 23 (transLenTr ⟨70, by decide⟩ 23 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_23.D1 (m := 1) from colCertDiv_147_70_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 23 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_23.D2 (m := 1) from colCertDiv_147_70_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_23_match


theorem leaf_147_70_24 (hp : 24 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 24 (transLenTr ⟨70, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 24 (transLenTr ⟨70, by decide⟩ 24 hp)) T147_70
      hfix147_70 hinj147_70 hcardT147_70
      (fun i => conj_mem_of_fixedPoints _ _ (T147_70 i) (hfix147_70 i) _)
      ⟨147, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 24 hp) Q2.T147_70_2 Q2.hfix147_70_2 Q2.hinj147_70_2
      Q2.hcardT147_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_70_2 i) (Q2.hfix147_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 24 (transLenTr ⟨70, by decide⟩ 24 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T147_70 = colFn colCertDiv_147_70_24.D1 (m := 1) from colCertDiv_147_70_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 24 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T147_70_2 = colFn colCertDiv_147_70_24.D2 (m := 1) from colCertDiv_147_70_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_70_24_match


theorem leaf_147_71_0 (hp : 0 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 0 (transLenTr ⟨71, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 0 (transLenTr ⟨71, by decide⟩ 0 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 0 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      colCert_147_71_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_71_1 (hp : 1 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 1 (transLenTr ⟨71, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 1 (transLenTr ⟨71, by decide⟩ 1 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 1 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      colCert_147_71_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_71_2 (hp : 2 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 2 (transLenTr ⟨71, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 2 (transLenTr ⟨71, by decide⟩ 2 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 2 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      colCert_147_71_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_71_3 (hp : 3 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 3 (transLenTr ⟨71, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 3 (transLenTr ⟨71, by decide⟩ 3 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 3 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      colCert_147_71_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_71_4 (hp : 4 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 4 (transLenTr ⟨71, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 4 (transLenTr ⟨71, by decide⟩ 4 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 4 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      colCert_147_71_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_71_5 (hp : 5 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 5 (transLenTr ⟨71, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 5 (transLenTr ⟨71, by decide⟩ 5 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 5 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 5 (transLenTr ⟨71, by decide⟩ 5 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_5.D1 (m := 1) from colCertDiv_147_71_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 5 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_5.D2 (m := 1) from colCertDiv_147_71_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_5_match


theorem leaf_147_71_6 (hp : 6 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 6 (transLenTr ⟨71, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 6 (transLenTr ⟨71, by decide⟩ 6 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 6 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 6 (transLenTr ⟨71, by decide⟩ 6 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_6.D1 (m := 1) from colCertDiv_147_71_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 6 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_6.D2 (m := 1) from colCertDiv_147_71_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_6_match


theorem leaf_147_71_7 (hp : 7 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 7 (transLenTr ⟨71, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 7 (transLenTr ⟨71, by decide⟩ 7 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 7 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 7 (transLenTr ⟨71, by decide⟩ 7 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_7.D1 (m := 1) from colCertDiv_147_71_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 7 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_7.D2 (m := 1) from colCertDiv_147_71_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_7_match


theorem leaf_147_71_8 (hp : 8 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 8 (transLenTr ⟨71, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 8 (transLenTr ⟨71, by decide⟩ 8 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 8 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 8 (transLenTr ⟨71, by decide⟩ 8 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_8.D1 (m := 1) from colCertDiv_147_71_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 8 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_8.D2 (m := 1) from colCertDiv_147_71_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_8_match


theorem leaf_147_71_9 (hp : 9 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 9 (transLenTr ⟨71, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 9 (transLenTr ⟨71, by decide⟩ 9 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 9 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 9 (transLenTr ⟨71, by decide⟩ 9 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_9.D1 (m := 1) from colCertDiv_147_71_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 9 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_9.D2 (m := 1) from colCertDiv_147_71_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_9_match


theorem leaf_147_71_10 (hp : 10 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 10 (transLenTr ⟨71, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 10 (transLenTr ⟨71, by decide⟩ 10 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 10 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 10 (transLenTr ⟨71, by decide⟩ 10 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_10.D1 (m := 1) from colCertDiv_147_71_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 10 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_10.D2 (m := 1) from colCertDiv_147_71_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_10_match


theorem leaf_147_71_11 (hp : 11 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 11 (transLenTr ⟨71, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 11 (transLenTr ⟨71, by decide⟩ 11 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 11 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 11 (transLenTr ⟨71, by decide⟩ 11 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_11.D1 (m := 1) from colCertDiv_147_71_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 11 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_11.D2 (m := 1) from colCertDiv_147_71_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_11_match


theorem leaf_147_71_12 (hp : 12 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 12 (transLenTr ⟨71, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 12 (transLenTr ⟨71, by decide⟩ 12 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 12 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 12 (transLenTr ⟨71, by decide⟩ 12 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_12.D1 (m := 1) from colCertDiv_147_71_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 12 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_12.D2 (m := 1) from colCertDiv_147_71_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_12_match


theorem leaf_147_71_13 (hp : 13 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 13 (transLenTr ⟨71, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 13 (transLenTr ⟨71, by decide⟩ 13 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 13 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 13 (transLenTr ⟨71, by decide⟩ 13 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_13.D1 (m := 1) from colCertDiv_147_71_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 13 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_13.D2 (m := 1) from colCertDiv_147_71_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_13_match


theorem leaf_147_71_14 (hp : 14 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 14 (transLenTr ⟨71, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 14 (transLenTr ⟨71, by decide⟩ 14 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 14 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 14 (transLenTr ⟨71, by decide⟩ 14 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_14.D1 (m := 1) from colCertDiv_147_71_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 14 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_14.D2 (m := 1) from colCertDiv_147_71_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_14_match


theorem leaf_147_71_15 (hp : 15 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 15 (transLenTr ⟨71, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 15 (transLenTr ⟨71, by decide⟩ 15 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 15 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 15 (transLenTr ⟨71, by decide⟩ 15 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_15.D1 (m := 1) from colCertDiv_147_71_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 15 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_15.D2 (m := 1) from colCertDiv_147_71_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_15_match


theorem leaf_147_71_16 (hp : 16 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 16 (transLenTr ⟨71, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 16 (transLenTr ⟨71, by decide⟩ 16 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 16 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 16 (transLenTr ⟨71, by decide⟩ 16 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_16.D1 (m := 1) from colCertDiv_147_71_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 16 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_16.D2 (m := 1) from colCertDiv_147_71_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_16_match


theorem leaf_147_71_17 (hp : 17 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 17 (transLenTr ⟨71, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 17 (transLenTr ⟨71, by decide⟩ 17 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 17 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 17 (transLenTr ⟨71, by decide⟩ 17 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_17.D1 (m := 1) from colCertDiv_147_71_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 17 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_17.D2 (m := 1) from colCertDiv_147_71_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_17_match


theorem leaf_147_71_18 (hp : 18 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 18 (transLenTr ⟨71, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 18 (transLenTr ⟨71, by decide⟩ 18 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 18 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 18 (transLenTr ⟨71, by decide⟩ 18 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_18.D1 (m := 1) from colCertDiv_147_71_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 18 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_18.D2 (m := 1) from colCertDiv_147_71_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_18_match


theorem leaf_147_71_19 (hp : 19 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 19 (transLenTr ⟨71, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 19 (transLenTr ⟨71, by decide⟩ 19 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 19 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 19 (transLenTr ⟨71, by decide⟩ 19 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_19.D1 (m := 1) from colCertDiv_147_71_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 19 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_19.D2 (m := 1) from colCertDiv_147_71_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_19_match


theorem leaf_147_71_20 (hp : 20 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 20 (transLenTr ⟨71, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 20 (transLenTr ⟨71, by decide⟩ 20 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 20 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 20 (transLenTr ⟨71, by decide⟩ 20 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_20.D1 (m := 1) from colCertDiv_147_71_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 20 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_20.D2 (m := 1) from colCertDiv_147_71_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_20_match


theorem leaf_147_71_21 (hp : 21 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 21 (transLenTr ⟨71, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 21 (transLenTr ⟨71, by decide⟩ 21 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 21 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 21 (transLenTr ⟨71, by decide⟩ 21 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_21.D1 (m := 1) from colCertDiv_147_71_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 21 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_21.D2 (m := 1) from colCertDiv_147_71_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_21_match


theorem leaf_147_71_22 (hp : 22 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 22 (transLenTr ⟨71, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 22 (transLenTr ⟨71, by decide⟩ 22 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 22 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 22 (transLenTr ⟨71, by decide⟩ 22 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_22.D1 (m := 1) from colCertDiv_147_71_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 22 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_22.D2 (m := 1) from colCertDiv_147_71_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_22_match


theorem leaf_147_71_23 (hp : 23 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 23 (transLenTr ⟨71, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 23 (transLenTr ⟨71, by decide⟩ 23 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 23 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 23 (transLenTr ⟨71, by decide⟩ 23 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_23.D1 (m := 1) from colCertDiv_147_71_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 23 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_23.D2 (m := 1) from colCertDiv_147_71_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_23_match


theorem leaf_147_71_24 (hp : 24 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 24 (transLenTr ⟨71, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 24 (transLenTr ⟨71, by decide⟩ 24 hp)) T147_71
      hfix147_71 hinj147_71 hcardT147_71
      (fun i => conj_mem_of_fixedPoints _ _ (T147_71 i) (hfix147_71 i) _)
      ⟨147, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 24 hp) Q2.T147_71_2 Q2.hfix147_71_2 Q2.hinj147_71_2
      Q2.hcardT147_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_71_2 i) (Q2.hfix147_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 24 (transLenTr ⟨71, by decide⟩ 24 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T147_71 = colFn colCertDiv_147_71_24.D1 (m := 1) from colCertDiv_147_71_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 24 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T147_71_2 = colFn colCertDiv_147_71_24.D2 (m := 1) from colCertDiv_147_71_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_71_24_match


theorem leaf_147_72_0 (hp : 0 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 0 (transLenTr ⟨72, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 0 (transLenTr ⟨72, by decide⟩ 0 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 0 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      colCert_147_72_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_72_1 (hp : 1 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 1 (transLenTr ⟨72, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 1 (transLenTr ⟨72, by decide⟩ 1 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 1 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      colCert_147_72_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_72_2 (hp : 2 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 2 (transLenTr ⟨72, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 2 (transLenTr ⟨72, by decide⟩ 2 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 2 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      colCert_147_72_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_72_3 (hp : 3 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 3 (transLenTr ⟨72, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 3 (transLenTr ⟨72, by decide⟩ 3 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 3 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      colCert_147_72_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_72_4 (hp : 4 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 4 (transLenTr ⟨72, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 4 (transLenTr ⟨72, by decide⟩ 4 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 4 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      colCert_147_72_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_72_5 (hp : 5 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 5 (transLenTr ⟨72, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 5 (transLenTr ⟨72, by decide⟩ 5 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 5 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 5 (transLenTr ⟨72, by decide⟩ 5 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_5.D1 (m := 1) from colCertDiv_147_72_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 5 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_5.D2 (m := 1) from colCertDiv_147_72_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_5_match


theorem leaf_147_72_6 (hp : 6 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 6 (transLenTr ⟨72, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 6 (transLenTr ⟨72, by decide⟩ 6 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 6 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 6 (transLenTr ⟨72, by decide⟩ 6 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_6.D1 (m := 1) from colCertDiv_147_72_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 6 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_6.D2 (m := 1) from colCertDiv_147_72_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_6_match


theorem leaf_147_72_7 (hp : 7 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 7 (transLenTr ⟨72, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 7 (transLenTr ⟨72, by decide⟩ 7 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 7 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 7 (transLenTr ⟨72, by decide⟩ 7 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_7.D1 (m := 1) from colCertDiv_147_72_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 7 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_7.D2 (m := 1) from colCertDiv_147_72_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_7_match


theorem leaf_147_72_8 (hp : 8 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 8 (transLenTr ⟨72, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 8 (transLenTr ⟨72, by decide⟩ 8 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 8 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 8 (transLenTr ⟨72, by decide⟩ 8 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_8.D1 (m := 1) from colCertDiv_147_72_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 8 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_8.D2 (m := 1) from colCertDiv_147_72_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_8_match


theorem leaf_147_72_9 (hp : 9 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 9 (transLenTr ⟨72, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 9 (transLenTr ⟨72, by decide⟩ 9 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 9 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 9 (transLenTr ⟨72, by decide⟩ 9 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_9.D1 (m := 1) from colCertDiv_147_72_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 9 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_9.D2 (m := 1) from colCertDiv_147_72_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_9_match


theorem leaf_147_72_10 (hp : 10 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 10 (transLenTr ⟨72, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 10 (transLenTr ⟨72, by decide⟩ 10 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 10 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 10 (transLenTr ⟨72, by decide⟩ 10 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_10.D1 (m := 1) from colCertDiv_147_72_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 10 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_10.D2 (m := 1) from colCertDiv_147_72_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_10_match


theorem leaf_147_72_11 (hp : 11 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 11 (transLenTr ⟨72, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 11 (transLenTr ⟨72, by decide⟩ 11 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 11 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 11 (transLenTr ⟨72, by decide⟩ 11 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_11.D1 (m := 1) from colCertDiv_147_72_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 11 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_11.D2 (m := 1) from colCertDiv_147_72_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_11_match


theorem leaf_147_72_12 (hp : 12 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 12 (transLenTr ⟨72, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 12 (transLenTr ⟨72, by decide⟩ 12 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 12 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 12 (transLenTr ⟨72, by decide⟩ 12 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_12.D1 (m := 1) from colCertDiv_147_72_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 12 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_12.D2 (m := 1) from colCertDiv_147_72_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_12_match


theorem leaf_147_72_13 (hp : 13 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 13 (transLenTr ⟨72, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 13 (transLenTr ⟨72, by decide⟩ 13 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 13 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 13 (transLenTr ⟨72, by decide⟩ 13 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_13.D1 (m := 1) from colCertDiv_147_72_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 13 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_13.D2 (m := 1) from colCertDiv_147_72_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_13_match


theorem leaf_147_72_14 (hp : 14 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 14 (transLenTr ⟨72, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 14 (transLenTr ⟨72, by decide⟩ 14 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 14 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 14 (transLenTr ⟨72, by decide⟩ 14 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_14.D1 (m := 1) from colCertDiv_147_72_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 14 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_14.D2 (m := 1) from colCertDiv_147_72_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_14_match


theorem leaf_147_72_15 (hp : 15 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 15 (transLenTr ⟨72, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 15 (transLenTr ⟨72, by decide⟩ 15 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 15 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 15 (transLenTr ⟨72, by decide⟩ 15 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_15.D1 (m := 1) from colCertDiv_147_72_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 15 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_15.D2 (m := 1) from colCertDiv_147_72_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_15_match


theorem leaf_147_72_16 (hp : 16 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 16 (transLenTr ⟨72, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 16 (transLenTr ⟨72, by decide⟩ 16 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 16 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 16 (transLenTr ⟨72, by decide⟩ 16 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_16.D1 (m := 1) from colCertDiv_147_72_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 16 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_16.D2 (m := 1) from colCertDiv_147_72_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_16_match


theorem leaf_147_72_17 (hp : 17 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 17 (transLenTr ⟨72, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 17 (transLenTr ⟨72, by decide⟩ 17 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 17 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 17 (transLenTr ⟨72, by decide⟩ 17 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_17.D1 (m := 1) from colCertDiv_147_72_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 17 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_17.D2 (m := 1) from colCertDiv_147_72_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_17_match


theorem leaf_147_72_18 (hp : 18 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 18 (transLenTr ⟨72, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 18 (transLenTr ⟨72, by decide⟩ 18 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 18 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 18 (transLenTr ⟨72, by decide⟩ 18 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_18.D1 (m := 1) from colCertDiv_147_72_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 18 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_18.D2 (m := 1) from colCertDiv_147_72_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_18_match


theorem leaf_147_72_19 (hp : 19 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 19 (transLenTr ⟨72, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 19 (transLenTr ⟨72, by decide⟩ 19 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 19 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 19 (transLenTr ⟨72, by decide⟩ 19 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_19.D1 (m := 1) from colCertDiv_147_72_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 19 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_19.D2 (m := 1) from colCertDiv_147_72_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_19_match


theorem leaf_147_72_20 (hp : 20 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 20 (transLenTr ⟨72, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 20 (transLenTr ⟨72, by decide⟩ 20 hp)) T147_72
      hfix147_72 hinj147_72 hcardT147_72
      (fun i => conj_mem_of_fixedPoints _ _ (T147_72 i) (hfix147_72 i) _)
      ⟨147, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 20 hp) Q2.T147_72_2 Q2.hfix147_72_2 Q2.hinj147_72_2
      Q2.hcardT147_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_72_2 i) (Q2.hfix147_72_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨72, by decide⟩ 20 (transLenTr ⟨72, by decide⟩ 20 hp) : ↥(reps ⟨72, by decide⟩)) : Coordinate 1)
        T147_72 = colFn colCertDiv_147_72_20.D1 (m := 1) from colCertDiv_147_72_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨72, by decide⟩ 20 hp : ↥(Q2.reps ⟨72, by decide⟩)) : Coordinate 2)
        Q2.T147_72_2 = colFn colCertDiv_147_72_20.D2 (m := 1) from colCertDiv_147_72_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_72_20_match


end LeanDring.P5Presentation
