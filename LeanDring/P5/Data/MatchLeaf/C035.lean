/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C012
import LeanDring.P5.Data.ColCdd.C013
import LeanDring.P5.Data.ColRestCheap.C061
import LeanDring.P5.Data.ColRestCheap.C062
import LeanDring.P5.Data.ColRestCheap.C063
import LeanDring.P5.Data.ColRestCheap.C064
import LeanDring.P5.Data.EntryK.C032
import LeanDring.P5.Data.EntryK.C033
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C012
import LeanDring.P5.Data.SpeciesDiv.C013
import LeanDring.P5.Data.SpeciesDiv.C014
import LeanDring.P5.Data.SpeciesDiv.C015

/-! # Stage-5 leaves, chunk 34 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_127_127_16 (hp : 16 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 16 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 16 (transLenTr ⟨127, by decide⟩ 16 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 16 (transLenTr ⟨127, by decide⟩ 16 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 16 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_16.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_17 (hp : 17 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 17 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 17 (transLenTr ⟨127, by decide⟩ 17 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 17 (transLenTr ⟨127, by decide⟩ 17 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 17 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_17.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_18 (hp : 18 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 18 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 18 (transLenTr ⟨127, by decide⟩ 18 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 18 (transLenTr ⟨127, by decide⟩ 18 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 18 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_18.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_19 (hp : 19 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 19 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 19 (transLenTr ⟨127, by decide⟩ 19 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 19 (transLenTr ⟨127, by decide⟩ 19 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 19 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_19.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_20 (hp : 20 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 20 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 20 (transLenTr ⟨127, by decide⟩ 20 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 20 (transLenTr ⟨127, by decide⟩ 20 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 20 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_20.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_21 (hp : 21 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 21 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 21 (transLenTr ⟨127, by decide⟩ 21 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 21 (transLenTr ⟨127, by decide⟩ 21 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 21 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_21.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_22 (hp : 22 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 22 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 22 (transLenTr ⟨127, by decide⟩ 22 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 22 (transLenTr ⟨127, by decide⟩ 22 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 22 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_22.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_23 (hp : 23 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 23 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 23 (transLenTr ⟨127, by decide⟩ 23 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 23 (transLenTr ⟨127, by decide⟩ 23 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 23 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_23.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_127_127_24 (hp : 24 < (Q2.transData.getD 127 []).length)
    (j : Nat) (hj : j < (repChars.getD 127 []).length)
    (hq : (normIsRep.getD 127 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ 24 hp)
        (rowE2 (⟨127, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ 24 (transLenTr ⟨127, by decide⟩ 24 hp))
        (rowE1 (⟨127, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨127, by decide⟩ : Fin 148) ⟨127, by decide⟩ _
      (validAt ⟨127, by decide⟩ (listedAt ⟨127, by decide⟩ hj))
      (colE1 ⟨127, by decide⟩ 24 (transLenTr ⟨127, by decide⟩ 24 hp)) T127_127
      hfix127_127 hinj127_127 hcardT127_127
      (fun i => conj_mem_of_fixedPoints _ _ (T127_127 i) (hfix127_127 i) _)
      ⟨127, by decide⟩ ⟨127, by decide⟩ _
      (Q2.validAt ⟨127, by decide⟩ (Q2.listedAt ⟨127, by decide⟩
        (alnCheck_rep ⟨127, by decide⟩ hj hq).1))
      (colE2 ⟨127, by decide⟩ 24 hp) Q2.T127_127_2 Q2.hfix127_127_2 Q2.hinj127_127_2
      Q2.hcardT127_127_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T127_127_2 i) (Q2.hfix127_127_2 i) _)
      colCert_127_127_24.hD ?_).symm
  rw [alnId_127 j hj]


theorem leaf_128_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T128_3
      hfix128_3 hinj128_3 hcardT128_3
      (fun i => conj_mem_of_fixedPoints _ _ (T128_3 i) (hfix128_3 i) _)
      ⟨128, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T128_3_2 Q2.hfix128_3_2 Q2.hinj128_3_2
      Q2.hcardT128_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_3_2 i) (Q2.hfix128_3_2 i) _)
      colCert_128_3_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T128_3
      hfix128_3 hinj128_3 hcardT128_3
      (fun i => conj_mem_of_fixedPoints _ _ (T128_3 i) (hfix128_3 i) _)
      ⟨128, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T128_3_2 Q2.hfix128_3_2 Q2.hinj128_3_2
      Q2.hcardT128_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_3_2 i) (Q2.hfix128_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T128_3 = colFn colCertDiv_128_3_1.D1 (m := 5) from colCertDiv_128_3_1.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 1 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T128_3_2 = colFn colCertDiv_128_3_1.D2 (m := 5) from colCertDiv_128_3_1.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_3_1_match


theorem leaf_128_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T128_3
      hfix128_3 hinj128_3 hcardT128_3
      (fun i => conj_mem_of_fixedPoints _ _ (T128_3 i) (hfix128_3 i) _)
      ⟨128, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T128_3_2 Q2.hfix128_3_2 Q2.hinj128_3_2
      Q2.hcardT128_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_3_2 i) (Q2.hfix128_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T128_3 = colFn colCertDiv_128_3_2.D1 (m := 5) from colCertDiv_128_3_2.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 2 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T128_3_2 = colFn colCertDiv_128_3_2.D2 (m := 5) from colCertDiv_128_3_2.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_3_2_match


theorem leaf_128_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T128_3
      hfix128_3 hinj128_3 hcardT128_3
      (fun i => conj_mem_of_fixedPoints _ _ (T128_3 i) (hfix128_3 i) _)
      ⟨128, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T128_3_2 Q2.hfix128_3_2 Q2.hinj128_3_2
      Q2.hcardT128_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_3_2 i) (Q2.hfix128_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T128_3 = colFn colCertDiv_128_3_3.D1 (m := 5) from colCertDiv_128_3_3.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 3 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T128_3_2 = colFn colCertDiv_128_3_3.D2 (m := 5) from colCertDiv_128_3_3.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_3_3_match


theorem leaf_128_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T128_3
      hfix128_3 hinj128_3 hcardT128_3
      (fun i => conj_mem_of_fixedPoints _ _ (T128_3 i) (hfix128_3 i) _)
      ⟨128, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T128_3_2 Q2.hfix128_3_2 Q2.hinj128_3_2
      Q2.hcardT128_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_3_2 i) (Q2.hfix128_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T128_3 = colFn colCertDiv_128_3_4.D1 (m := 5) from colCertDiv_128_3_4.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 4 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T128_3_2 = colFn colCertDiv_128_3_4.D2 (m := 5) from colCertDiv_128_3_4.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_3_4_match


theorem leaf_128_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T128_10
      hfix128_10 hinj128_10 hcardT128_10
      (fun i => conj_mem_of_fixedPoints _ _ (T128_10 i) (hfix128_10 i) _)
      ⟨128, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T128_10_2 Q2.hfix128_10_2 Q2.hinj128_10_2
      Q2.hcardT128_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_10_2 i) (Q2.hfix128_10_2 i) _)
      colCert_128_10_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T128_10
      hfix128_10 hinj128_10 hcardT128_10
      (fun i => conj_mem_of_fixedPoints _ _ (T128_10 i) (hfix128_10 i) _)
      ⟨128, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T128_10_2 Q2.hfix128_10_2 Q2.hinj128_10_2
      Q2.hcardT128_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_10_2 i) (Q2.hfix128_10_2 i) _)
      colCert_128_10_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T128_10
      hfix128_10 hinj128_10 hcardT128_10
      (fun i => conj_mem_of_fixedPoints _ _ (T128_10 i) (hfix128_10 i) _)
      ⟨128, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T128_10_2 Q2.hfix128_10_2 Q2.hinj128_10_2
      Q2.hcardT128_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_10_2 i) (Q2.hfix128_10_2 i) _)
      colCert_128_10_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T128_10
      hfix128_10 hinj128_10 hcardT128_10
      (fun i => conj_mem_of_fixedPoints _ _ (T128_10 i) (hfix128_10 i) _)
      ⟨128, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T128_10_2 Q2.hfix128_10_2 Q2.hinj128_10_2
      Q2.hcardT128_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_10_2 i) (Q2.hfix128_10_2 i) _)
      colCert_128_10_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T128_10
      hfix128_10 hinj128_10 hcardT128_10
      (fun i => conj_mem_of_fixedPoints _ _ (T128_10 i) (hfix128_10 i) _)
      ⟨128, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T128_10_2 Q2.hfix128_10_2 Q2.hinj128_10_2
      Q2.hcardT128_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_10_2 i) (Q2.hfix128_10_2 i) _)
      colCert_128_10_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T128_12
      hfix128_12 hinj128_12 hcardT128_12
      (fun i => conj_mem_of_fixedPoints _ _ (T128_12 i) (hfix128_12 i) _)
      ⟨128, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T128_12_2 Q2.hfix128_12_2 Q2.hinj128_12_2
      Q2.hcardT128_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_12_2 i) (Q2.hfix128_12_2 i) _)
      colCert_128_12_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T128_12
      hfix128_12 hinj128_12 hcardT128_12
      (fun i => conj_mem_of_fixedPoints _ _ (T128_12 i) (hfix128_12 i) _)
      ⟨128, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T128_12_2 Q2.hfix128_12_2 Q2.hinj128_12_2
      Q2.hcardT128_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_12_2 i) (Q2.hfix128_12_2 i) _)
      colCert_128_12_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T128_12
      hfix128_12 hinj128_12 hcardT128_12
      (fun i => conj_mem_of_fixedPoints _ _ (T128_12 i) (hfix128_12 i) _)
      ⟨128, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T128_12_2 Q2.hfix128_12_2 Q2.hinj128_12_2
      Q2.hcardT128_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_12_2 i) (Q2.hfix128_12_2 i) _)
      colCert_128_12_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T128_12
      hfix128_12 hinj128_12 hcardT128_12
      (fun i => conj_mem_of_fixedPoints _ _ (T128_12 i) (hfix128_12 i) _)
      ⟨128, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T128_12_2 Q2.hfix128_12_2 Q2.hinj128_12_2
      Q2.hcardT128_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_12_2 i) (Q2.hfix128_12_2 i) _)
      colCert_128_12_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T128_12
      hfix128_12 hinj128_12 hcardT128_12
      (fun i => conj_mem_of_fixedPoints _ _ (T128_12 i) (hfix128_12 i) _)
      ⟨128, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T128_12_2 Q2.hfix128_12_2 Q2.hinj128_12_2
      Q2.hcardT128_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_12_2 i) (Q2.hfix128_12_2 i) _)
      colCert_128_12_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T128_21
      hfix128_21 hinj128_21 hcardT128_21
      (fun i => conj_mem_of_fixedPoints _ _ (T128_21 i) (hfix128_21 i) _)
      ⟨128, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T128_21_2 Q2.hfix128_21_2 Q2.hinj128_21_2
      Q2.hcardT128_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_21_2 i) (Q2.hfix128_21_2 i) _)
      colCert_128_21_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T128_21
      hfix128_21 hinj128_21 hcardT128_21
      (fun i => conj_mem_of_fixedPoints _ _ (T128_21 i) (hfix128_21 i) _)
      ⟨128, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T128_21_2 Q2.hfix128_21_2 Q2.hinj128_21_2
      Q2.hcardT128_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_21_2 i) (Q2.hfix128_21_2 i) _)
      colCert_128_21_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T128_21
      hfix128_21 hinj128_21 hcardT128_21
      (fun i => conj_mem_of_fixedPoints _ _ (T128_21 i) (hfix128_21 i) _)
      ⟨128, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T128_21_2 Q2.hfix128_21_2 Q2.hinj128_21_2
      Q2.hcardT128_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_21_2 i) (Q2.hfix128_21_2 i) _)
      colCert_128_21_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T128_21
      hfix128_21 hinj128_21 hcardT128_21
      (fun i => conj_mem_of_fixedPoints _ _ (T128_21 i) (hfix128_21 i) _)
      ⟨128, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T128_21_2 Q2.hfix128_21_2 Q2.hinj128_21_2
      Q2.hcardT128_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_21_2 i) (Q2.hfix128_21_2 i) _)
      colCert_128_21_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T128_21
      hfix128_21 hinj128_21 hcardT128_21
      (fun i => conj_mem_of_fixedPoints _ _ (T128_21 i) (hfix128_21 i) _)
      ⟨128, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T128_21_2 Q2.hfix128_21_2 Q2.hinj128_21_2
      Q2.hcardT128_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_21_2 i) (Q2.hfix128_21_2 i) _)
      colCert_128_21_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T128_21
      hfix128_21 hinj128_21 hcardT128_21
      (fun i => conj_mem_of_fixedPoints _ _ (T128_21 i) (hfix128_21 i) _)
      ⟨128, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T128_21_2 Q2.hfix128_21_2 Q2.hinj128_21_2
      Q2.hcardT128_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_21_2 i) (Q2.hfix128_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T128_21 = colFn colCertDiv_128_21_5.D1 (m := 5) from colCertDiv_128_21_5.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 5 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T128_21_2 = colFn colCertDiv_128_21_5.D2 (m := 5) from colCertDiv_128_21_5.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_21_5_match


theorem leaf_128_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T128_21
      hfix128_21 hinj128_21 hcardT128_21
      (fun i => conj_mem_of_fixedPoints _ _ (T128_21 i) (hfix128_21 i) _)
      ⟨128, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T128_21_2 Q2.hfix128_21_2 Q2.hinj128_21_2
      Q2.hcardT128_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_21_2 i) (Q2.hfix128_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T128_21 = colFn colCertDiv_128_21_10.D1 (m := 5) from colCertDiv_128_21_10.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 10 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T128_21_2 = colFn colCertDiv_128_21_10.D2 (m := 5) from colCertDiv_128_21_10.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_21_10_match


theorem leaf_128_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T128_21
      hfix128_21 hinj128_21 hcardT128_21
      (fun i => conj_mem_of_fixedPoints _ _ (T128_21 i) (hfix128_21 i) _)
      ⟨128, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T128_21_2 Q2.hfix128_21_2 Q2.hinj128_21_2
      Q2.hcardT128_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_21_2 i) (Q2.hfix128_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T128_21 = colFn colCertDiv_128_21_15.D1 (m := 5) from colCertDiv_128_21_15.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 15 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T128_21_2 = colFn colCertDiv_128_21_15.D2 (m := 5) from colCertDiv_128_21_15.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_21_15_match


theorem leaf_128_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T128_21
      hfix128_21 hinj128_21 hcardT128_21
      (fun i => conj_mem_of_fixedPoints _ _ (T128_21 i) (hfix128_21 i) _)
      ⟨128, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T128_21_2 Q2.hfix128_21_2 Q2.hinj128_21_2
      Q2.hcardT128_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_21_2 i) (Q2.hfix128_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T128_21 = colFn colCertDiv_128_21_20.D1 (m := 5) from colCertDiv_128_21_20.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 20 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T128_21_2 = colFn colCertDiv_128_21_20.D2 (m := 5) from colCertDiv_128_21_20.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_21_20_match


theorem leaf_128_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T128_28
      hfix128_28 hinj128_28 hcardT128_28
      (fun i => conj_mem_of_fixedPoints _ _ (T128_28 i) (hfix128_28 i) _)
      ⟨128, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T128_28_2 Q2.hfix128_28_2 Q2.hinj128_28_2
      Q2.hcardT128_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_28_2 i) (Q2.hfix128_28_2 i) _)
      colCert_128_28_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T128_28
      hfix128_28 hinj128_28 hcardT128_28
      (fun i => conj_mem_of_fixedPoints _ _ (T128_28 i) (hfix128_28 i) _)
      ⟨128, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T128_28_2 Q2.hfix128_28_2 Q2.hinj128_28_2
      Q2.hcardT128_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_28_2 i) (Q2.hfix128_28_2 i) _)
      colCert_128_28_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T128_28
      hfix128_28 hinj128_28 hcardT128_28
      (fun i => conj_mem_of_fixedPoints _ _ (T128_28 i) (hfix128_28 i) _)
      ⟨128, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T128_28_2 Q2.hfix128_28_2 Q2.hinj128_28_2
      Q2.hcardT128_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_28_2 i) (Q2.hfix128_28_2 i) _)
      colCert_128_28_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T128_28
      hfix128_28 hinj128_28 hcardT128_28
      (fun i => conj_mem_of_fixedPoints _ _ (T128_28 i) (hfix128_28 i) _)
      ⟨128, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T128_28_2 Q2.hfix128_28_2 Q2.hinj128_28_2
      Q2.hcardT128_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_28_2 i) (Q2.hfix128_28_2 i) _)
      colCert_128_28_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T128_28
      hfix128_28 hinj128_28 hcardT128_28
      (fun i => conj_mem_of_fixedPoints _ _ (T128_28 i) (hfix128_28 i) _)
      ⟨128, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T128_28_2 Q2.hfix128_28_2 Q2.hinj128_28_2
      Q2.hcardT128_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_28_2 i) (Q2.hfix128_28_2 i) _)
      colCert_128_28_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T128_28
      hfix128_28 hinj128_28 hcardT128_28
      (fun i => conj_mem_of_fixedPoints _ _ (T128_28 i) (hfix128_28 i) _)
      ⟨128, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T128_28_2 Q2.hfix128_28_2 Q2.hinj128_28_2
      Q2.hcardT128_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_28_2 i) (Q2.hfix128_28_2 i) _)
      colCert_128_28_5.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T128_28
      hfix128_28 hinj128_28 hcardT128_28
      (fun i => conj_mem_of_fixedPoints _ _ (T128_28 i) (hfix128_28 i) _)
      ⟨128, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T128_28_2 Q2.hfix128_28_2 Q2.hinj128_28_2
      Q2.hcardT128_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_28_2 i) (Q2.hfix128_28_2 i) _)
      colCert_128_28_10.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T128_28
      hfix128_28 hinj128_28 hcardT128_28
      (fun i => conj_mem_of_fixedPoints _ _ (T128_28 i) (hfix128_28 i) _)
      ⟨128, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T128_28_2 Q2.hfix128_28_2 Q2.hinj128_28_2
      Q2.hcardT128_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_28_2 i) (Q2.hfix128_28_2 i) _)
      colCert_128_28_15.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T128_28
      hfix128_28 hinj128_28 hcardT128_28
      (fun i => conj_mem_of_fixedPoints _ _ (T128_28 i) (hfix128_28 i) _)
      ⟨128, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T128_28_2 Q2.hfix128_28_2 Q2.hinj128_28_2
      Q2.hcardT128_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_28_2 i) (Q2.hfix128_28_2 i) _)
      colCert_128_28_20.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T128_34
      hfix128_34 hinj128_34 hcardT128_34
      (fun i => conj_mem_of_fixedPoints _ _ (T128_34 i) (hfix128_34 i) _)
      ⟨128, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T128_34_2 Q2.hfix128_34_2 Q2.hinj128_34_2
      Q2.hcardT128_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_34_2 i) (Q2.hfix128_34_2 i) _)
      colCert_128_34_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T128_34
      hfix128_34 hinj128_34 hcardT128_34
      (fun i => conj_mem_of_fixedPoints _ _ (T128_34 i) (hfix128_34 i) _)
      ⟨128, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T128_34_2 Q2.hfix128_34_2 Q2.hinj128_34_2
      Q2.hcardT128_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_34_2 i) (Q2.hfix128_34_2 i) _)
      colCert_128_34_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T128_34
      hfix128_34 hinj128_34 hcardT128_34
      (fun i => conj_mem_of_fixedPoints _ _ (T128_34 i) (hfix128_34 i) _)
      ⟨128, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T128_34_2 Q2.hfix128_34_2 Q2.hinj128_34_2
      Q2.hcardT128_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_34_2 i) (Q2.hfix128_34_2 i) _)
      colCert_128_34_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T128_34
      hfix128_34 hinj128_34 hcardT128_34
      (fun i => conj_mem_of_fixedPoints _ _ (T128_34 i) (hfix128_34 i) _)
      ⟨128, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T128_34_2 Q2.hfix128_34_2 Q2.hinj128_34_2
      Q2.hcardT128_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_34_2 i) (Q2.hfix128_34_2 i) _)
      colCert_128_34_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T128_34
      hfix128_34 hinj128_34 hcardT128_34
      (fun i => conj_mem_of_fixedPoints _ _ (T128_34 i) (hfix128_34 i) _)
      ⟨128, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T128_34_2 Q2.hfix128_34_2 Q2.hinj128_34_2
      Q2.hcardT128_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_34_2 i) (Q2.hfix128_34_2 i) _)
      colCert_128_34_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T128_34
      hfix128_34 hinj128_34 hcardT128_34
      (fun i => conj_mem_of_fixedPoints _ _ (T128_34 i) (hfix128_34 i) _)
      ⟨128, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T128_34_2 Q2.hfix128_34_2 Q2.hinj128_34_2
      Q2.hcardT128_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_34_2 i) (Q2.hfix128_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T128_34 = colFn colCertDiv_128_34_5.D1 (m := 5) from colCertDiv_128_34_5.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 5 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T128_34_2 = colFn colCertDiv_128_34_5.D2 (m := 5) from colCertDiv_128_34_5.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_34_5_match


theorem leaf_128_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T128_34
      hfix128_34 hinj128_34 hcardT128_34
      (fun i => conj_mem_of_fixedPoints _ _ (T128_34 i) (hfix128_34 i) _)
      ⟨128, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T128_34_2 Q2.hfix128_34_2 Q2.hinj128_34_2
      Q2.hcardT128_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_34_2 i) (Q2.hfix128_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T128_34 = colFn colCertDiv_128_34_10.D1 (m := 5) from colCertDiv_128_34_10.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 10 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T128_34_2 = colFn colCertDiv_128_34_10.D2 (m := 5) from colCertDiv_128_34_10.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_34_10_match


theorem leaf_128_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T128_34
      hfix128_34 hinj128_34 hcardT128_34
      (fun i => conj_mem_of_fixedPoints _ _ (T128_34 i) (hfix128_34 i) _)
      ⟨128, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T128_34_2 Q2.hfix128_34_2 Q2.hinj128_34_2
      Q2.hcardT128_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_34_2 i) (Q2.hfix128_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T128_34 = colFn colCertDiv_128_34_15.D1 (m := 5) from colCertDiv_128_34_15.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 15 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T128_34_2 = colFn colCertDiv_128_34_15.D2 (m := 5) from colCertDiv_128_34_15.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_34_15_match


theorem leaf_128_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T128_34
      hfix128_34 hinj128_34 hcardT128_34
      (fun i => conj_mem_of_fixedPoints _ _ (T128_34 i) (hfix128_34 i) _)
      ⟨128, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T128_34_2 Q2.hfix128_34_2 Q2.hinj128_34_2
      Q2.hcardT128_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_34_2 i) (Q2.hfix128_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T128_34 = colFn colCertDiv_128_34_20.D1 (m := 5) from colCertDiv_128_34_20.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 20 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T128_34_2 = colFn colCertDiv_128_34_20.D2 (m := 5) from colCertDiv_128_34_20.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_34_20_match


theorem leaf_128_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T128_41
      hfix128_41 hinj128_41 hcardT128_41
      (fun i => conj_mem_of_fixedPoints _ _ (T128_41 i) (hfix128_41 i) _)
      ⟨128, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T128_41_2 Q2.hfix128_41_2 Q2.hinj128_41_2
      Q2.hcardT128_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_41_2 i) (Q2.hfix128_41_2 i) _)
      colCert_128_41_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T128_41
      hfix128_41 hinj128_41 hcardT128_41
      (fun i => conj_mem_of_fixedPoints _ _ (T128_41 i) (hfix128_41 i) _)
      ⟨128, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T128_41_2 Q2.hfix128_41_2 Q2.hinj128_41_2
      Q2.hcardT128_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_41_2 i) (Q2.hfix128_41_2 i) _)
      colCert_128_41_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T128_41
      hfix128_41 hinj128_41 hcardT128_41
      (fun i => conj_mem_of_fixedPoints _ _ (T128_41 i) (hfix128_41 i) _)
      ⟨128, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T128_41_2 Q2.hfix128_41_2 Q2.hinj128_41_2
      Q2.hcardT128_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_41_2 i) (Q2.hfix128_41_2 i) _)
      colCert_128_41_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T128_41
      hfix128_41 hinj128_41 hcardT128_41
      (fun i => conj_mem_of_fixedPoints _ _ (T128_41 i) (hfix128_41 i) _)
      ⟨128, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T128_41_2 Q2.hfix128_41_2 Q2.hinj128_41_2
      Q2.hcardT128_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_41_2 i) (Q2.hfix128_41_2 i) _)
      colCert_128_41_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T128_41
      hfix128_41 hinj128_41 hcardT128_41
      (fun i => conj_mem_of_fixedPoints _ _ (T128_41 i) (hfix128_41 i) _)
      ⟨128, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T128_41_2 Q2.hfix128_41_2 Q2.hinj128_41_2
      Q2.hcardT128_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_41_2 i) (Q2.hfix128_41_2 i) _)
      colCert_128_41_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T128_41
      hfix128_41 hinj128_41 hcardT128_41
      (fun i => conj_mem_of_fixedPoints _ _ (T128_41 i) (hfix128_41 i) _)
      ⟨128, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T128_41_2 Q2.hfix128_41_2 Q2.hinj128_41_2
      Q2.hcardT128_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_41_2 i) (Q2.hfix128_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T128_41 = colFn colCertDiv_128_41_5.D1 (m := 5) from colCertDiv_128_41_5.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 5 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T128_41_2 = colFn colCertDiv_128_41_5.D2 (m := 5) from colCertDiv_128_41_5.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_41_5_match


theorem leaf_128_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T128_41
      hfix128_41 hinj128_41 hcardT128_41
      (fun i => conj_mem_of_fixedPoints _ _ (T128_41 i) (hfix128_41 i) _)
      ⟨128, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T128_41_2 Q2.hfix128_41_2 Q2.hinj128_41_2
      Q2.hcardT128_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_41_2 i) (Q2.hfix128_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T128_41 = colFn colCertDiv_128_41_10.D1 (m := 5) from colCertDiv_128_41_10.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 10 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T128_41_2 = colFn colCertDiv_128_41_10.D2 (m := 5) from colCertDiv_128_41_10.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_41_10_match


theorem leaf_128_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T128_41
      hfix128_41 hinj128_41 hcardT128_41
      (fun i => conj_mem_of_fixedPoints _ _ (T128_41 i) (hfix128_41 i) _)
      ⟨128, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T128_41_2 Q2.hfix128_41_2 Q2.hinj128_41_2
      Q2.hcardT128_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_41_2 i) (Q2.hfix128_41_2 i) _)
      colCert_128_41_15.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T128_41
      hfix128_41 hinj128_41 hcardT128_41
      (fun i => conj_mem_of_fixedPoints _ _ (T128_41 i) (hfix128_41 i) _)
      ⟨128, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T128_41_2 Q2.hfix128_41_2 Q2.hinj128_41_2
      Q2.hcardT128_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_41_2 i) (Q2.hfix128_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T128_41 = colFn colCertDiv_128_41_20.D1 (m := 5) from colCertDiv_128_41_20.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 20 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T128_41_2 = colFn colCertDiv_128_41_20.D2 (m := 5) from colCertDiv_128_41_20.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_41_20_match


theorem leaf_128_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T128_47
      hfix128_47 hinj128_47 hcardT128_47
      (fun i => conj_mem_of_fixedPoints _ _ (T128_47 i) (hfix128_47 i) _)
      ⟨128, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T128_47_2 Q2.hfix128_47_2 Q2.hinj128_47_2
      Q2.hcardT128_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_47_2 i) (Q2.hfix128_47_2 i) _)
      colCert_128_47_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T128_47
      hfix128_47 hinj128_47 hcardT128_47
      (fun i => conj_mem_of_fixedPoints _ _ (T128_47 i) (hfix128_47 i) _)
      ⟨128, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T128_47_2 Q2.hfix128_47_2 Q2.hinj128_47_2
      Q2.hcardT128_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_47_2 i) (Q2.hfix128_47_2 i) _)
      colCert_128_47_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T128_47
      hfix128_47 hinj128_47 hcardT128_47
      (fun i => conj_mem_of_fixedPoints _ _ (T128_47 i) (hfix128_47 i) _)
      ⟨128, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T128_47_2 Q2.hfix128_47_2 Q2.hinj128_47_2
      Q2.hcardT128_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_47_2 i) (Q2.hfix128_47_2 i) _)
      colCert_128_47_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T128_47
      hfix128_47 hinj128_47 hcardT128_47
      (fun i => conj_mem_of_fixedPoints _ _ (T128_47 i) (hfix128_47 i) _)
      ⟨128, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T128_47_2 Q2.hfix128_47_2 Q2.hinj128_47_2
      Q2.hcardT128_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_47_2 i) (Q2.hfix128_47_2 i) _)
      colCert_128_47_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T128_47
      hfix128_47 hinj128_47 hcardT128_47
      (fun i => conj_mem_of_fixedPoints _ _ (T128_47 i) (hfix128_47 i) _)
      ⟨128, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T128_47_2 Q2.hfix128_47_2 Q2.hinj128_47_2
      Q2.hcardT128_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_47_2 i) (Q2.hfix128_47_2 i) _)
      colCert_128_47_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T128_47
      hfix128_47 hinj128_47 hcardT128_47
      (fun i => conj_mem_of_fixedPoints _ _ (T128_47 i) (hfix128_47 i) _)
      ⟨128, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T128_47_2 Q2.hfix128_47_2 Q2.hinj128_47_2
      Q2.hcardT128_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_47_2 i) (Q2.hfix128_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T128_47 = colFn colCertDiv_128_47_5.D1 (m := 5) from colCertDiv_128_47_5.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T128_47_2 = colFn colCertDiv_128_47_5.D2 (m := 5) from colCertDiv_128_47_5.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_47_5_match


theorem leaf_128_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T128_47
      hfix128_47 hinj128_47 hcardT128_47
      (fun i => conj_mem_of_fixedPoints _ _ (T128_47 i) (hfix128_47 i) _)
      ⟨128, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T128_47_2 Q2.hfix128_47_2 Q2.hinj128_47_2
      Q2.hcardT128_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_47_2 i) (Q2.hfix128_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T128_47 = colFn colCertDiv_128_47_10.D1 (m := 5) from colCertDiv_128_47_10.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T128_47_2 = colFn colCertDiv_128_47_10.D2 (m := 5) from colCertDiv_128_47_10.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_47_10_match


theorem leaf_128_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T128_47
      hfix128_47 hinj128_47 hcardT128_47
      (fun i => conj_mem_of_fixedPoints _ _ (T128_47 i) (hfix128_47 i) _)
      ⟨128, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T128_47_2 Q2.hfix128_47_2 Q2.hinj128_47_2
      Q2.hcardT128_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_47_2 i) (Q2.hfix128_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T128_47 = colFn colCertDiv_128_47_15.D1 (m := 5) from colCertDiv_128_47_15.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T128_47_2 = colFn colCertDiv_128_47_15.D2 (m := 5) from colCertDiv_128_47_15.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_47_15_match


theorem leaf_128_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T128_47
      hfix128_47 hinj128_47 hcardT128_47
      (fun i => conj_mem_of_fixedPoints _ _ (T128_47 i) (hfix128_47 i) _)
      ⟨128, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T128_47_2 Q2.hfix128_47_2 Q2.hinj128_47_2
      Q2.hcardT128_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_47_2 i) (Q2.hfix128_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T128_47 = colFn colCertDiv_128_47_20.D1 (m := 5) from colCertDiv_128_47_20.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T128_47_2 = colFn colCertDiv_128_47_20.D2 (m := 5) from colCertDiv_128_47_20.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_47_20_match


theorem leaf_128_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T128_50
      hfix128_50 hinj128_50 hcardT128_50
      (fun i => conj_mem_of_fixedPoints _ _ (T128_50 i) (hfix128_50 i) _)
      ⟨128, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T128_50_2 Q2.hfix128_50_2 Q2.hinj128_50_2
      Q2.hcardT128_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_50_2 i) (Q2.hfix128_50_2 i) _)
      colCert_128_50_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T128_50
      hfix128_50 hinj128_50 hcardT128_50
      (fun i => conj_mem_of_fixedPoints _ _ (T128_50 i) (hfix128_50 i) _)
      ⟨128, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T128_50_2 Q2.hfix128_50_2 Q2.hinj128_50_2
      Q2.hcardT128_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_50_2 i) (Q2.hfix128_50_2 i) _)
      colCert_128_50_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T128_50
      hfix128_50 hinj128_50 hcardT128_50
      (fun i => conj_mem_of_fixedPoints _ _ (T128_50 i) (hfix128_50 i) _)
      ⟨128, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T128_50_2 Q2.hfix128_50_2 Q2.hinj128_50_2
      Q2.hcardT128_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_50_2 i) (Q2.hfix128_50_2 i) _)
      colCert_128_50_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T128_50
      hfix128_50 hinj128_50 hcardT128_50
      (fun i => conj_mem_of_fixedPoints _ _ (T128_50 i) (hfix128_50 i) _)
      ⟨128, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T128_50_2 Q2.hfix128_50_2 Q2.hinj128_50_2
      Q2.hcardT128_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_50_2 i) (Q2.hfix128_50_2 i) _)
      colCert_128_50_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T128_50
      hfix128_50 hinj128_50 hcardT128_50
      (fun i => conj_mem_of_fixedPoints _ _ (T128_50 i) (hfix128_50 i) _)
      ⟨128, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T128_50_2 Q2.hfix128_50_2 Q2.hinj128_50_2
      Q2.hcardT128_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_50_2 i) (Q2.hfix128_50_2 i) _)
      colCert_128_50_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T128_50
      hfix128_50 hinj128_50 hcardT128_50
      (fun i => conj_mem_of_fixedPoints _ _ (T128_50 i) (hfix128_50 i) _)
      ⟨128, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T128_50_2 Q2.hfix128_50_2 Q2.hinj128_50_2
      Q2.hcardT128_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_50_2 i) (Q2.hfix128_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T128_50 = colFn colCertDiv_128_50_5.D1 (m := 5) from colCertDiv_128_50_5.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 5 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T128_50_2 = colFn colCertDiv_128_50_5.D2 (m := 5) from colCertDiv_128_50_5.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_50_5_match


theorem leaf_128_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T128_50
      hfix128_50 hinj128_50 hcardT128_50
      (fun i => conj_mem_of_fixedPoints _ _ (T128_50 i) (hfix128_50 i) _)
      ⟨128, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T128_50_2 Q2.hfix128_50_2 Q2.hinj128_50_2
      Q2.hcardT128_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_50_2 i) (Q2.hfix128_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T128_50 = colFn colCertDiv_128_50_10.D1 (m := 5) from colCertDiv_128_50_10.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 10 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T128_50_2 = colFn colCertDiv_128_50_10.D2 (m := 5) from colCertDiv_128_50_10.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_50_10_match


theorem leaf_128_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T128_50
      hfix128_50 hinj128_50 hcardT128_50
      (fun i => conj_mem_of_fixedPoints _ _ (T128_50 i) (hfix128_50 i) _)
      ⟨128, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T128_50_2 Q2.hfix128_50_2 Q2.hinj128_50_2
      Q2.hcardT128_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_50_2 i) (Q2.hfix128_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T128_50 = colFn colCertDiv_128_50_15.D1 (m := 5) from colCertDiv_128_50_15.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 15 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T128_50_2 = colFn colCertDiv_128_50_15.D2 (m := 5) from colCertDiv_128_50_15.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_50_15_match


theorem leaf_128_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T128_50
      hfix128_50 hinj128_50 hcardT128_50
      (fun i => conj_mem_of_fixedPoints _ _ (T128_50 i) (hfix128_50 i) _)
      ⟨128, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T128_50_2 Q2.hfix128_50_2 Q2.hinj128_50_2
      Q2.hcardT128_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_50_2 i) (Q2.hfix128_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T128_50 = colFn colCertDiv_128_50_20.D1 (m := 5) from colCertDiv_128_50_20.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 20 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T128_50_2 = colFn colCertDiv_128_50_20.D2 (m := 5) from colCertDiv_128_50_20.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_50_20_match


theorem leaf_128_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T128_53
      hfix128_53 hinj128_53 hcardT128_53
      (fun i => conj_mem_of_fixedPoints _ _ (T128_53 i) (hfix128_53 i) _)
      ⟨128, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T128_53_2 Q2.hfix128_53_2 Q2.hinj128_53_2
      Q2.hcardT128_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_53_2 i) (Q2.hfix128_53_2 i) _)
      colCert_128_53_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T128_53
      hfix128_53 hinj128_53 hcardT128_53
      (fun i => conj_mem_of_fixedPoints _ _ (T128_53 i) (hfix128_53 i) _)
      ⟨128, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T128_53_2 Q2.hfix128_53_2 Q2.hinj128_53_2
      Q2.hcardT128_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_53_2 i) (Q2.hfix128_53_2 i) _)
      colCert_128_53_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T128_53
      hfix128_53 hinj128_53 hcardT128_53
      (fun i => conj_mem_of_fixedPoints _ _ (T128_53 i) (hfix128_53 i) _)
      ⟨128, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T128_53_2 Q2.hfix128_53_2 Q2.hinj128_53_2
      Q2.hcardT128_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_53_2 i) (Q2.hfix128_53_2 i) _)
      colCert_128_53_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T128_53
      hfix128_53 hinj128_53 hcardT128_53
      (fun i => conj_mem_of_fixedPoints _ _ (T128_53 i) (hfix128_53 i) _)
      ⟨128, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T128_53_2 Q2.hfix128_53_2 Q2.hinj128_53_2
      Q2.hcardT128_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_53_2 i) (Q2.hfix128_53_2 i) _)
      colCert_128_53_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T128_53
      hfix128_53 hinj128_53 hcardT128_53
      (fun i => conj_mem_of_fixedPoints _ _ (T128_53 i) (hfix128_53 i) _)
      ⟨128, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T128_53_2 Q2.hfix128_53_2 Q2.hinj128_53_2
      Q2.hcardT128_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_53_2 i) (Q2.hfix128_53_2 i) _)
      colCert_128_53_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T128_53
      hfix128_53 hinj128_53 hcardT128_53
      (fun i => conj_mem_of_fixedPoints _ _ (T128_53 i) (hfix128_53 i) _)
      ⟨128, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T128_53_2 Q2.hfix128_53_2 Q2.hinj128_53_2
      Q2.hcardT128_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_53_2 i) (Q2.hfix128_53_2 i) _)
      colCert_128_53_5.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T128_53
      hfix128_53 hinj128_53 hcardT128_53
      (fun i => conj_mem_of_fixedPoints _ _ (T128_53 i) (hfix128_53 i) _)
      ⟨128, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T128_53_2 Q2.hfix128_53_2 Q2.hinj128_53_2
      Q2.hcardT128_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_53_2 i) (Q2.hfix128_53_2 i) _)
      colCert_128_53_10.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T128_53
      hfix128_53 hinj128_53 hcardT128_53
      (fun i => conj_mem_of_fixedPoints _ _ (T128_53 i) (hfix128_53 i) _)
      ⟨128, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T128_53_2 Q2.hfix128_53_2 Q2.hinj128_53_2
      Q2.hcardT128_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_53_2 i) (Q2.hfix128_53_2 i) _)
      colCert_128_53_15.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T128_53
      hfix128_53 hinj128_53 hcardT128_53
      (fun i => conj_mem_of_fixedPoints _ _ (T128_53 i) (hfix128_53 i) _)
      ⟨128, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T128_53_2 Q2.hfix128_53_2 Q2.hinj128_53_2
      Q2.hcardT128_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_53_2 i) (Q2.hfix128_53_2 i) _)
      colCert_128_53_20.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_82_0 (hp : 0 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp)) T128_82
      hfix128_82 hinj128_82 hcardT128_82
      (fun i => conj_mem_of_fixedPoints _ _ (T128_82 i) (hfix128_82 i) _)
      ⟨128, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 0 hp) Q2.T128_82_2 Q2.hfix128_82_2 Q2.hinj128_82_2
      Q2.hcardT128_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_82_2 i) (Q2.hfix128_82_2 i) _)
      colCert_128_82_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_82_1 (hp : 1 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp)) T128_82
      hfix128_82 hinj128_82 hcardT128_82
      (fun i => conj_mem_of_fixedPoints _ _ (T128_82 i) (hfix128_82 i) _)
      ⟨128, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 1 hp) Q2.T128_82_2 Q2.hfix128_82_2 Q2.hinj128_82_2
      Q2.hcardT128_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_82_2 i) (Q2.hfix128_82_2 i) _)
      colCert_128_82_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_82_2 (hp : 2 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp)) T128_82
      hfix128_82 hinj128_82 hcardT128_82
      (fun i => conj_mem_of_fixedPoints _ _ (T128_82 i) (hfix128_82 i) _)
      ⟨128, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 2 hp) Q2.T128_82_2 Q2.hfix128_82_2 Q2.hinj128_82_2
      Q2.hcardT128_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_82_2 i) (Q2.hfix128_82_2 i) _)
      colCert_128_82_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_82_3 (hp : 3 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp)) T128_82
      hfix128_82 hinj128_82 hcardT128_82
      (fun i => conj_mem_of_fixedPoints _ _ (T128_82 i) (hfix128_82 i) _)
      ⟨128, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 3 hp) Q2.T128_82_2 Q2.hfix128_82_2 Q2.hinj128_82_2
      Q2.hcardT128_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_82_2 i) (Q2.hfix128_82_2 i) _)
      colCert_128_82_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_82_4 (hp : 4 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp)) T128_82
      hfix128_82 hinj128_82 hcardT128_82
      (fun i => conj_mem_of_fixedPoints _ _ (T128_82 i) (hfix128_82 i) _)
      ⟨128, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 4 hp) Q2.T128_82_2 Q2.hfix128_82_2 Q2.hinj128_82_2
      Q2.hcardT128_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_82_2 i) (Q2.hfix128_82_2 i) _)
      colCert_128_82_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_82_5 (hp : 5 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp)) T128_82
      hfix128_82 hinj128_82 hcardT128_82
      (fun i => conj_mem_of_fixedPoints _ _ (T128_82 i) (hfix128_82 i) _)
      ⟨128, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 5 hp) Q2.T128_82_2 Q2.hfix128_82_2 Q2.hinj128_82_2
      Q2.hcardT128_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_82_2 i) (Q2.hfix128_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T128_82 = colFn colCertDiv_128_82_5.D1 (m := 5) from colCertDiv_128_82_5.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 5 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T128_82_2 = colFn colCertDiv_128_82_5.D2 (m := 5) from colCertDiv_128_82_5.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_82_5_match


theorem leaf_128_82_10 (hp : 10 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp)) T128_82
      hfix128_82 hinj128_82 hcardT128_82
      (fun i => conj_mem_of_fixedPoints _ _ (T128_82 i) (hfix128_82 i) _)
      ⟨128, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 10 hp) Q2.T128_82_2 Q2.hfix128_82_2 Q2.hinj128_82_2
      Q2.hcardT128_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_82_2 i) (Q2.hfix128_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T128_82 = colFn colCertDiv_128_82_10.D1 (m := 5) from colCertDiv_128_82_10.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 10 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T128_82_2 = colFn colCertDiv_128_82_10.D2 (m := 5) from colCertDiv_128_82_10.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_82_10_match


theorem leaf_128_82_15 (hp : 15 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp)) T128_82
      hfix128_82 hinj128_82 hcardT128_82
      (fun i => conj_mem_of_fixedPoints _ _ (T128_82 i) (hfix128_82 i) _)
      ⟨128, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 15 hp) Q2.T128_82_2 Q2.hfix128_82_2 Q2.hinj128_82_2
      Q2.hcardT128_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_82_2 i) (Q2.hfix128_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T128_82 = colFn colCertDiv_128_82_15.D1 (m := 5) from colCertDiv_128_82_15.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 15 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T128_82_2 = colFn colCertDiv_128_82_15.D2 (m := 5) from colCertDiv_128_82_15.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_82_15_match


theorem leaf_128_82_20 (hp : 20 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp)) T128_82
      hfix128_82 hinj128_82 hcardT128_82
      (fun i => conj_mem_of_fixedPoints _ _ (T128_82 i) (hfix128_82 i) _)
      ⟨128, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 20 hp) Q2.T128_82_2 Q2.hfix128_82_2 Q2.hinj128_82_2
      Q2.hcardT128_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_82_2 i) (Q2.hfix128_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T128_82 = colFn colCertDiv_128_82_20.D1 (m := 5) from colCertDiv_128_82_20.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 20 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T128_82_2 = colFn colCertDiv_128_82_20.D2 (m := 5) from colCertDiv_128_82_20.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_82_20_match


theorem leaf_128_90_0 (hp : 0 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 0 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      colCert_128_90_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_90_1 (hp : 1 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 1 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      colCert_128_90_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_90_2 (hp : 2 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 2 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      colCert_128_90_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_90_3 (hp : 3 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 3 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      colCert_128_90_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_90_4 (hp : 4 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 4 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      colCert_128_90_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_90_5 (hp : 5 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 5 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      colCert_128_90_5.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_90_10 (hp : 10 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 10 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      colCert_128_90_10.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_90_15 (hp : 15 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 15 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      colCert_128_90_15.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_90_20 (hp : 20 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 20 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      colCert_128_90_20.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_90_25 (hp : 25 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 25 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 25 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T128_90 = colFn colCertDiv_128_90_25.D1 (m := 5) from colCertDiv_128_90_25.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 25 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T128_90_2 = colFn colCertDiv_128_90_25.D2 (m := 5) from colCertDiv_128_90_25.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_90_25_match


theorem leaf_128_90_50 (hp : 50 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 50 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 50 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T128_90 = colFn colCertDiv_128_90_50.D1 (m := 5) from colCertDiv_128_90_50.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 50 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T128_90_2 = colFn colCertDiv_128_90_50.D2 (m := 5) from colCertDiv_128_90_50.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_90_50_match


theorem leaf_128_90_75 (hp : 75 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 75 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 75 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T128_90 = colFn colCertDiv_128_90_75.D1 (m := 5) from colCertDiv_128_90_75.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 75 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T128_90_2 = colFn colCertDiv_128_90_75.D2 (m := 5) from colCertDiv_128_90_75.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_90_75_match


theorem leaf_128_90_100 (hp : 100 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 100 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp)) T128_90
      hfix128_90 hinj128_90 hcardT128_90
      (fun i => conj_mem_of_fixedPoints _ _ (T128_90 i) (hfix128_90 i) _)
      ⟨128, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 100 hp) Q2.T128_90_2 Q2.hfix128_90_2 Q2.hinj128_90_2
      Q2.hcardT128_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_90_2 i) (Q2.hfix128_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T128_90 = colFn colCertDiv_128_90_100.D1 (m := 5) from colCertDiv_128_90_100.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 100 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T128_90_2 = colFn colCertDiv_128_90_100.D2 (m := 5) from colCertDiv_128_90_100.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_90_100_match


theorem leaf_128_96_0 (hp : 0 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp)) T128_96
      hfix128_96 hinj128_96 hcardT128_96
      (fun i => conj_mem_of_fixedPoints _ _ (T128_96 i) (hfix128_96 i) _)
      ⟨128, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 0 hp) Q2.T128_96_2 Q2.hfix128_96_2 Q2.hinj128_96_2
      Q2.hcardT128_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_96_2 i) (Q2.hfix128_96_2 i) _)
      colCert_128_96_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_96_1 (hp : 1 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp)) T128_96
      hfix128_96 hinj128_96 hcardT128_96
      (fun i => conj_mem_of_fixedPoints _ _ (T128_96 i) (hfix128_96 i) _)
      ⟨128, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 1 hp) Q2.T128_96_2 Q2.hfix128_96_2 Q2.hinj128_96_2
      Q2.hcardT128_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_96_2 i) (Q2.hfix128_96_2 i) _)
      colCert_128_96_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_96_2 (hp : 2 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp)) T128_96
      hfix128_96 hinj128_96 hcardT128_96
      (fun i => conj_mem_of_fixedPoints _ _ (T128_96 i) (hfix128_96 i) _)
      ⟨128, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 2 hp) Q2.T128_96_2 Q2.hfix128_96_2 Q2.hinj128_96_2
      Q2.hcardT128_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_96_2 i) (Q2.hfix128_96_2 i) _)
      colCert_128_96_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_96_3 (hp : 3 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp)) T128_96
      hfix128_96 hinj128_96 hcardT128_96
      (fun i => conj_mem_of_fixedPoints _ _ (T128_96 i) (hfix128_96 i) _)
      ⟨128, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 3 hp) Q2.T128_96_2 Q2.hfix128_96_2 Q2.hinj128_96_2
      Q2.hcardT128_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_96_2 i) (Q2.hfix128_96_2 i) _)
      colCert_128_96_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_96_4 (hp : 4 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp)) T128_96
      hfix128_96 hinj128_96 hcardT128_96
      (fun i => conj_mem_of_fixedPoints _ _ (T128_96 i) (hfix128_96 i) _)
      ⟨128, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 4 hp) Q2.T128_96_2 Q2.hfix128_96_2 Q2.hinj128_96_2
      Q2.hcardT128_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_96_2 i) (Q2.hfix128_96_2 i) _)
      colCert_128_96_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_96_5 (hp : 5 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp)) T128_96
      hfix128_96 hinj128_96 hcardT128_96
      (fun i => conj_mem_of_fixedPoints _ _ (T128_96 i) (hfix128_96 i) _)
      ⟨128, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 5 hp) Q2.T128_96_2 Q2.hfix128_96_2 Q2.hinj128_96_2
      Q2.hcardT128_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_96_2 i) (Q2.hfix128_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T128_96 = colFn colCertDiv_128_96_5.D1 (m := 5) from colCertDiv_128_96_5.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 5 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T128_96_2 = colFn colCertDiv_128_96_5.D2 (m := 5) from colCertDiv_128_96_5.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_96_5_match


theorem leaf_128_96_10 (hp : 10 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp)) T128_96
      hfix128_96 hinj128_96 hcardT128_96
      (fun i => conj_mem_of_fixedPoints _ _ (T128_96 i) (hfix128_96 i) _)
      ⟨128, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 10 hp) Q2.T128_96_2 Q2.hfix128_96_2 Q2.hinj128_96_2
      Q2.hcardT128_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_96_2 i) (Q2.hfix128_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T128_96 = colFn colCertDiv_128_96_10.D1 (m := 5) from colCertDiv_128_96_10.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 10 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T128_96_2 = colFn colCertDiv_128_96_10.D2 (m := 5) from colCertDiv_128_96_10.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_96_10_match


theorem leaf_128_96_15 (hp : 15 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp)) T128_96
      hfix128_96 hinj128_96 hcardT128_96
      (fun i => conj_mem_of_fixedPoints _ _ (T128_96 i) (hfix128_96 i) _)
      ⟨128, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 15 hp) Q2.T128_96_2 Q2.hfix128_96_2 Q2.hinj128_96_2
      Q2.hcardT128_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_96_2 i) (Q2.hfix128_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T128_96 = colFn colCertDiv_128_96_15.D1 (m := 5) from colCertDiv_128_96_15.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 15 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T128_96_2 = colFn colCertDiv_128_96_15.D2 (m := 5) from colCertDiv_128_96_15.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_96_15_match


theorem leaf_128_96_20 (hp : 20 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp)) T128_96
      hfix128_96 hinj128_96 hcardT128_96
      (fun i => conj_mem_of_fixedPoints _ _ (T128_96 i) (hfix128_96 i) _)
      ⟨128, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 20 hp) Q2.T128_96_2 Q2.hfix128_96_2 Q2.hinj128_96_2
      Q2.hcardT128_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_96_2 i) (Q2.hfix128_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T128_96 = colFn colCertDiv_128_96_20.D1 (m := 5) from colCertDiv_128_96_20.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 20 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T128_96_2 = colFn colCertDiv_128_96_20.D2 (m := 5) from colCertDiv_128_96_20.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_96_20_match


theorem leaf_128_103_0 (hp : 0 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp)) T128_103
      hfix128_103 hinj128_103 hcardT128_103
      (fun i => conj_mem_of_fixedPoints _ _ (T128_103 i) (hfix128_103 i) _)
      ⟨128, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 0 hp) Q2.T128_103_2 Q2.hfix128_103_2 Q2.hinj128_103_2
      Q2.hcardT128_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_103_2 i) (Q2.hfix128_103_2 i) _)
      colCert_128_103_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_103_1 (hp : 1 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp)) T128_103
      hfix128_103 hinj128_103 hcardT128_103
      (fun i => conj_mem_of_fixedPoints _ _ (T128_103 i) (hfix128_103 i) _)
      ⟨128, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 1 hp) Q2.T128_103_2 Q2.hfix128_103_2 Q2.hinj128_103_2
      Q2.hcardT128_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_103_2 i) (Q2.hfix128_103_2 i) _)
      colCert_128_103_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_103_2 (hp : 2 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp)) T128_103
      hfix128_103 hinj128_103 hcardT128_103
      (fun i => conj_mem_of_fixedPoints _ _ (T128_103 i) (hfix128_103 i) _)
      ⟨128, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 2 hp) Q2.T128_103_2 Q2.hfix128_103_2 Q2.hinj128_103_2
      Q2.hcardT128_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_103_2 i) (Q2.hfix128_103_2 i) _)
      colCert_128_103_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_103_3 (hp : 3 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp)) T128_103
      hfix128_103 hinj128_103 hcardT128_103
      (fun i => conj_mem_of_fixedPoints _ _ (T128_103 i) (hfix128_103 i) _)
      ⟨128, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 3 hp) Q2.T128_103_2 Q2.hfix128_103_2 Q2.hinj128_103_2
      Q2.hcardT128_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_103_2 i) (Q2.hfix128_103_2 i) _)
      colCert_128_103_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_103_4 (hp : 4 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp)) T128_103
      hfix128_103 hinj128_103 hcardT128_103
      (fun i => conj_mem_of_fixedPoints _ _ (T128_103 i) (hfix128_103 i) _)
      ⟨128, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 4 hp) Q2.T128_103_2 Q2.hfix128_103_2 Q2.hinj128_103_2
      Q2.hcardT128_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_103_2 i) (Q2.hfix128_103_2 i) _)
      colCert_128_103_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_103_5 (hp : 5 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp)) T128_103
      hfix128_103 hinj128_103 hcardT128_103
      (fun i => conj_mem_of_fixedPoints _ _ (T128_103 i) (hfix128_103 i) _)
      ⟨128, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 5 hp) Q2.T128_103_2 Q2.hfix128_103_2 Q2.hinj128_103_2
      Q2.hcardT128_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_103_2 i) (Q2.hfix128_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 5 (transLenTr ⟨103, by decide⟩ 5 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T128_103 = colFn colCertDiv_128_103_5.D1 (m := 5) from colCertDiv_128_103_5.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 5 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T128_103_2 = colFn colCertDiv_128_103_5.D2 (m := 5) from colCertDiv_128_103_5.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_103_5_match


theorem leaf_128_103_10 (hp : 10 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 10 (transLenTr ⟨103, by decide⟩ 10 hp)) T128_103
      hfix128_103 hinj128_103 hcardT128_103
      (fun i => conj_mem_of_fixedPoints _ _ (T128_103 i) (hfix128_103 i) _)
      ⟨128, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 10 hp) Q2.T128_103_2 Q2.hfix128_103_2 Q2.hinj128_103_2
      Q2.hcardT128_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_103_2 i) (Q2.hfix128_103_2 i) _)
      colCert_128_103_10.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_103_15 (hp : 15 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp)) T128_103
      hfix128_103 hinj128_103 hcardT128_103
      (fun i => conj_mem_of_fixedPoints _ _ (T128_103 i) (hfix128_103 i) _)
      ⟨128, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 15 hp) Q2.T128_103_2 Q2.hfix128_103_2 Q2.hinj128_103_2
      Q2.hcardT128_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_103_2 i) (Q2.hfix128_103_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨103, by decide⟩ 15 (transLenTr ⟨103, by decide⟩ 15 hp) : ↥(reps ⟨103, by decide⟩)) : Coordinate 1)
        T128_103 = colFn colCertDiv_128_103_15.D1 (m := 5) from colCertDiv_128_103_15.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨103, by decide⟩ 15 hp : ↥(Q2.reps ⟨103, by decide⟩)) : Coordinate 2)
        Q2.T128_103_2 = colFn colCertDiv_128_103_15.D2 (m := 5) from colCertDiv_128_103_15.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_103_15_match


theorem leaf_128_103_20 (hp : 20 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 20 (transLenTr ⟨103, by decide⟩ 20 hp)) T128_103
      hfix128_103 hinj128_103 hcardT128_103
      (fun i => conj_mem_of_fixedPoints _ _ (T128_103 i) (hfix128_103 i) _)
      ⟨128, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 20 hp) Q2.T128_103_2 Q2.hfix128_103_2 Q2.hinj128_103_2
      Q2.hcardT128_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_103_2 i) (Q2.hfix128_103_2 i) _)
      colCert_128_103_20.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_109_0 (hp : 0 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 0 (transLenTr ⟨109, by decide⟩ 0 hp)) T128_109
      hfix128_109 hinj128_109 hcardT128_109
      (fun i => conj_mem_of_fixedPoints _ _ (T128_109 i) (hfix128_109 i) _)
      ⟨128, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 0 hp) Q2.T128_109_2 Q2.hfix128_109_2 Q2.hinj128_109_2
      Q2.hcardT128_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_109_2 i) (Q2.hfix128_109_2 i) _)
      colCert_128_109_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_109_1 (hp : 1 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 1 (transLenTr ⟨109, by decide⟩ 1 hp)) T128_109
      hfix128_109 hinj128_109 hcardT128_109
      (fun i => conj_mem_of_fixedPoints _ _ (T128_109 i) (hfix128_109 i) _)
      ⟨128, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 1 hp) Q2.T128_109_2 Q2.hfix128_109_2 Q2.hinj128_109_2
      Q2.hcardT128_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_109_2 i) (Q2.hfix128_109_2 i) _)
      colCert_128_109_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_109_2 (hp : 2 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 2 (transLenTr ⟨109, by decide⟩ 2 hp)) T128_109
      hfix128_109 hinj128_109 hcardT128_109
      (fun i => conj_mem_of_fixedPoints _ _ (T128_109 i) (hfix128_109 i) _)
      ⟨128, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 2 hp) Q2.T128_109_2 Q2.hfix128_109_2 Q2.hinj128_109_2
      Q2.hcardT128_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_109_2 i) (Q2.hfix128_109_2 i) _)
      colCert_128_109_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_109_3 (hp : 3 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 3 (transLenTr ⟨109, by decide⟩ 3 hp)) T128_109
      hfix128_109 hinj128_109 hcardT128_109
      (fun i => conj_mem_of_fixedPoints _ _ (T128_109 i) (hfix128_109 i) _)
      ⟨128, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 3 hp) Q2.T128_109_2 Q2.hfix128_109_2 Q2.hinj128_109_2
      Q2.hcardT128_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_109_2 i) (Q2.hfix128_109_2 i) _)
      colCert_128_109_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_109_4 (hp : 4 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 4 (transLenTr ⟨109, by decide⟩ 4 hp)) T128_109
      hfix128_109 hinj128_109 hcardT128_109
      (fun i => conj_mem_of_fixedPoints _ _ (T128_109 i) (hfix128_109 i) _)
      ⟨128, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 4 hp) Q2.T128_109_2 Q2.hfix128_109_2 Q2.hinj128_109_2
      Q2.hcardT128_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_109_2 i) (Q2.hfix128_109_2 i) _)
      colCert_128_109_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_109_5 (hp : 5 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp)) T128_109
      hfix128_109 hinj128_109 hcardT128_109
      (fun i => conj_mem_of_fixedPoints _ _ (T128_109 i) (hfix128_109 i) _)
      ⟨128, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 5 hp) Q2.T128_109_2 Q2.hfix128_109_2 Q2.hinj128_109_2
      Q2.hcardT128_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_109_2 i) (Q2.hfix128_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 5 (transLenTr ⟨109, by decide⟩ 5 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T128_109 = colFn colCertDiv_128_109_5.D1 (m := 5) from colCertDiv_128_109_5.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 5 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T128_109_2 = colFn colCertDiv_128_109_5.D2 (m := 5) from colCertDiv_128_109_5.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_109_5_match


theorem leaf_128_109_10 (hp : 10 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp)) T128_109
      hfix128_109 hinj128_109 hcardT128_109
      (fun i => conj_mem_of_fixedPoints _ _ (T128_109 i) (hfix128_109 i) _)
      ⟨128, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 10 hp) Q2.T128_109_2 Q2.hfix128_109_2 Q2.hinj128_109_2
      Q2.hcardT128_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_109_2 i) (Q2.hfix128_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 10 (transLenTr ⟨109, by decide⟩ 10 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T128_109 = colFn colCertDiv_128_109_10.D1 (m := 5) from colCertDiv_128_109_10.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 10 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T128_109_2 = colFn colCertDiv_128_109_10.D2 (m := 5) from colCertDiv_128_109_10.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_109_10_match


theorem leaf_128_109_15 (hp : 15 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp)) T128_109
      hfix128_109 hinj128_109 hcardT128_109
      (fun i => conj_mem_of_fixedPoints _ _ (T128_109 i) (hfix128_109 i) _)
      ⟨128, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 15 hp) Q2.T128_109_2 Q2.hfix128_109_2 Q2.hinj128_109_2
      Q2.hcardT128_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_109_2 i) (Q2.hfix128_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 15 (transLenTr ⟨109, by decide⟩ 15 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T128_109 = colFn colCertDiv_128_109_15.D1 (m := 5) from colCertDiv_128_109_15.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 15 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T128_109_2 = colFn colCertDiv_128_109_15.D2 (m := 5) from colCertDiv_128_109_15.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_109_15_match


theorem leaf_128_109_20 (hp : 20 < (Q2.transData.getD 109 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨109, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp)) T128_109
      hfix128_109 hinj128_109 hcardT128_109
      (fun i => conj_mem_of_fixedPoints _ _ (T128_109 i) (hfix128_109 i) _)
      ⟨128, by decide⟩ ⟨109, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨109, by decide⟩ 20 hp) Q2.T128_109_2 Q2.hfix128_109_2 Q2.hinj128_109_2
      Q2.hcardT128_109_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_109_2 i) (Q2.hfix128_109_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨109, by decide⟩ 20 (transLenTr ⟨109, by decide⟩ 20 hp) : ↥(reps ⟨109, by decide⟩)) : Coordinate 1)
        T128_109 = colFn colCertDiv_128_109_20.D1 (m := 5) from colCertDiv_128_109_20.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨109, by decide⟩ 20 hp : ↥(Q2.reps ⟨109, by decide⟩)) : Coordinate 2)
        Q2.T128_109_2 = colFn colCertDiv_128_109_20.D2 (m := 5) from colCertDiv_128_109_20.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_109_20_match


theorem leaf_128_112_0 (hp : 0 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 0 (transLenTr ⟨112, by decide⟩ 0 hp)) T128_112
      hfix128_112 hinj128_112 hcardT128_112
      (fun i => conj_mem_of_fixedPoints _ _ (T128_112 i) (hfix128_112 i) _)
      ⟨128, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 0 hp) Q2.T128_112_2 Q2.hfix128_112_2 Q2.hinj128_112_2
      Q2.hcardT128_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_112_2 i) (Q2.hfix128_112_2 i) _)
      colCert_128_112_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_112_1 (hp : 1 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 1 (transLenTr ⟨112, by decide⟩ 1 hp)) T128_112
      hfix128_112 hinj128_112 hcardT128_112
      (fun i => conj_mem_of_fixedPoints _ _ (T128_112 i) (hfix128_112 i) _)
      ⟨128, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 1 hp) Q2.T128_112_2 Q2.hfix128_112_2 Q2.hinj128_112_2
      Q2.hcardT128_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_112_2 i) (Q2.hfix128_112_2 i) _)
      colCert_128_112_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_112_2 (hp : 2 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 2 (transLenTr ⟨112, by decide⟩ 2 hp)) T128_112
      hfix128_112 hinj128_112 hcardT128_112
      (fun i => conj_mem_of_fixedPoints _ _ (T128_112 i) (hfix128_112 i) _)
      ⟨128, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 2 hp) Q2.T128_112_2 Q2.hfix128_112_2 Q2.hinj128_112_2
      Q2.hcardT128_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_112_2 i) (Q2.hfix128_112_2 i) _)
      colCert_128_112_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_112_3 (hp : 3 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 3 (transLenTr ⟨112, by decide⟩ 3 hp)) T128_112
      hfix128_112 hinj128_112 hcardT128_112
      (fun i => conj_mem_of_fixedPoints _ _ (T128_112 i) (hfix128_112 i) _)
      ⟨128, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 3 hp) Q2.T128_112_2 Q2.hfix128_112_2 Q2.hinj128_112_2
      Q2.hcardT128_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_112_2 i) (Q2.hfix128_112_2 i) _)
      colCert_128_112_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_112_4 (hp : 4 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 4 (transLenTr ⟨112, by decide⟩ 4 hp)) T128_112
      hfix128_112 hinj128_112 hcardT128_112
      (fun i => conj_mem_of_fixedPoints _ _ (T128_112 i) (hfix128_112 i) _)
      ⟨128, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 4 hp) Q2.T128_112_2 Q2.hfix128_112_2 Q2.hinj128_112_2
      Q2.hcardT128_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_112_2 i) (Q2.hfix128_112_2 i) _)
      colCert_128_112_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_112_5 (hp : 5 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 5 (transLenTr ⟨112, by decide⟩ 5 hp)) T128_112
      hfix128_112 hinj128_112 hcardT128_112
      (fun i => conj_mem_of_fixedPoints _ _ (T128_112 i) (hfix128_112 i) _)
      ⟨128, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 5 hp) Q2.T128_112_2 Q2.hfix128_112_2 Q2.hinj128_112_2
      Q2.hcardT128_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_112_2 i) (Q2.hfix128_112_2 i) _)
      colCert_128_112_5.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_112_10 (hp : 10 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 10 (transLenTr ⟨112, by decide⟩ 10 hp)) T128_112
      hfix128_112 hinj128_112 hcardT128_112
      (fun i => conj_mem_of_fixedPoints _ _ (T128_112 i) (hfix128_112 i) _)
      ⟨128, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 10 hp) Q2.T128_112_2 Q2.hfix128_112_2 Q2.hinj128_112_2
      Q2.hcardT128_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_112_2 i) (Q2.hfix128_112_2 i) _)
      colCert_128_112_10.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_112_15 (hp : 15 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp)) T128_112
      hfix128_112 hinj128_112 hcardT128_112
      (fun i => conj_mem_of_fixedPoints _ _ (T128_112 i) (hfix128_112 i) _)
      ⟨128, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 15 hp) Q2.T128_112_2 Q2.hfix128_112_2 Q2.hinj128_112_2
      Q2.hcardT128_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_112_2 i) (Q2.hfix128_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 15 (transLenTr ⟨112, by decide⟩ 15 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T128_112 = colFn colCertDiv_128_112_15.D1 (m := 5) from colCertDiv_128_112_15.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 15 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T128_112_2 = colFn colCertDiv_128_112_15.D2 (m := 5) from colCertDiv_128_112_15.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_112_15_match


theorem leaf_128_112_20 (hp : 20 < (Q2.transData.getD 112 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨128, by decide⟩ : Fin 148) ⟨112, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp)) T128_112
      hfix128_112 hinj128_112 hcardT128_112
      (fun i => conj_mem_of_fixedPoints _ _ (T128_112 i) (hfix128_112 i) _)
      ⟨128, by decide⟩ ⟨112, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨112, by decide⟩ 20 hp) Q2.T128_112_2 Q2.hfix128_112_2 Q2.hinj128_112_2
      Q2.hcardT128_112_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_112_2 i) (Q2.hfix128_112_2 i) _)
      ?_).symm
  rw [show colData1 (⟨128, by decide⟩ : Fin 148)
        ((colE1 ⟨112, by decide⟩ 20 (transLenTr ⟨112, by decide⟩ 20 hp) : ↥(reps ⟨112, by decide⟩)) : Coordinate 1)
        T128_112 = colFn colCertDiv_128_112_20.D1 (m := 5) from colCertDiv_128_112_20.bind1,
    show colData2 (⟨128, by decide⟩ : Fin 148)
        ((colE2 ⟨112, by decide⟩ 20 hp : ↥(Q2.reps ⟨112, by decide⟩)) : Coordinate 2)
        Q2.T128_112_2 = colFn colCertDiv_128_112_20.D2 (m := 5) from colCertDiv_128_112_20.bind2]
  rw [alnId_128 j hj]
  exact fastcode_of_div ⟨128, by decide⟩ _ _ _
    ((alnId_128 j hj) ▸ Q2.listedAt (⟨128, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨128, by decide⟩ : Fin 148) hj hq).1) colCertDiv_128_112_20_match


theorem leaf_128_128_0 (hp : 0 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 0 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 0 (transLenTr ⟨128, by decide⟩ 0 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 0 (transLenTr ⟨128, by decide⟩ 0 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 0 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_0.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_1 (hp : 1 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 1 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 1 (transLenTr ⟨128, by decide⟩ 1 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 1 (transLenTr ⟨128, by decide⟩ 1 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 1 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_1.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_2 (hp : 2 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 2 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 2 (transLenTr ⟨128, by decide⟩ 2 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 2 (transLenTr ⟨128, by decide⟩ 2 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 2 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_2.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_3 (hp : 3 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 3 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 3 (transLenTr ⟨128, by decide⟩ 3 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 3 (transLenTr ⟨128, by decide⟩ 3 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 3 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_3.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_4 (hp : 4 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 4 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 4 (transLenTr ⟨128, by decide⟩ 4 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 4 (transLenTr ⟨128, by decide⟩ 4 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 4 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_4.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_5 (hp : 5 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 5 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 5 (transLenTr ⟨128, by decide⟩ 5 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 5 (transLenTr ⟨128, by decide⟩ 5 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 5 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_5.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_6 (hp : 6 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 6 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 6 (transLenTr ⟨128, by decide⟩ 6 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 6 (transLenTr ⟨128, by decide⟩ 6 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 6 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_6.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_7 (hp : 7 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 7 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 7 (transLenTr ⟨128, by decide⟩ 7 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 7 (transLenTr ⟨128, by decide⟩ 7 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 7 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_7.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_8 (hp : 8 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 8 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 8 (transLenTr ⟨128, by decide⟩ 8 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 8 (transLenTr ⟨128, by decide⟩ 8 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 8 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_8.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_9 (hp : 9 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 9 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 9 (transLenTr ⟨128, by decide⟩ 9 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 9 (transLenTr ⟨128, by decide⟩ 9 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 9 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_9.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_10 (hp : 10 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 10 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 10 (transLenTr ⟨128, by decide⟩ 10 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 10 (transLenTr ⟨128, by decide⟩ 10 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 10 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_10.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_11 (hp : 11 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 11 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 11 (transLenTr ⟨128, by decide⟩ 11 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 11 (transLenTr ⟨128, by decide⟩ 11 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 11 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_11.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_12 (hp : 12 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 12 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 12 (transLenTr ⟨128, by decide⟩ 12 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 12 (transLenTr ⟨128, by decide⟩ 12 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 12 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_12.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_13 (hp : 13 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 13 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 13 (transLenTr ⟨128, by decide⟩ 13 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 13 (transLenTr ⟨128, by decide⟩ 13 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 13 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_13.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_14 (hp : 14 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 14 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 14 (transLenTr ⟨128, by decide⟩ 14 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 14 (transLenTr ⟨128, by decide⟩ 14 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 14 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_14.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_15 (hp : 15 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 15 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 15 (transLenTr ⟨128, by decide⟩ 15 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 15 (transLenTr ⟨128, by decide⟩ 15 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 15 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_15.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_16 (hp : 16 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 16 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 16 (transLenTr ⟨128, by decide⟩ 16 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 16 (transLenTr ⟨128, by decide⟩ 16 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 16 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_16.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_17 (hp : 17 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 17 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 17 (transLenTr ⟨128, by decide⟩ 17 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 17 (transLenTr ⟨128, by decide⟩ 17 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 17 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_17.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_18 (hp : 18 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 18 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 18 (transLenTr ⟨128, by decide⟩ 18 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 18 (transLenTr ⟨128, by decide⟩ 18 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 18 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_18.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_19 (hp : 19 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 19 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 19 (transLenTr ⟨128, by decide⟩ 19 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 19 (transLenTr ⟨128, by decide⟩ 19 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 19 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_19.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_20 (hp : 20 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 20 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 20 (transLenTr ⟨128, by decide⟩ 20 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 20 (transLenTr ⟨128, by decide⟩ 20 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 20 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_20.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_21 (hp : 21 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 21 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 21 (transLenTr ⟨128, by decide⟩ 21 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 21 (transLenTr ⟨128, by decide⟩ 21 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 21 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_21.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_22 (hp : 22 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 22 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 22 (transLenTr ⟨128, by decide⟩ 22 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 22 (transLenTr ⟨128, by decide⟩ 22 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 22 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_22.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_23 (hp : 23 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 23 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 23 (transLenTr ⟨128, by decide⟩ 23 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 23 (transLenTr ⟨128, by decide⟩ 23 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 23 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_23.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_128_128_24 (hp : 24 < (Q2.transData.getD 128 []).length)
    (j : Nat) (hj : j < (repChars.getD 128 []).length)
    (hq : (normIsRep.getD 128 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ 24 hp)
        (rowE2 (⟨128, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ 24 (transLenTr ⟨128, by decide⟩ 24 hp))
        (rowE1 (⟨128, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨128, by decide⟩ : Fin 148) ⟨128, by decide⟩ _
      (validAt ⟨128, by decide⟩ (listedAt ⟨128, by decide⟩ hj))
      (colE1 ⟨128, by decide⟩ 24 (transLenTr ⟨128, by decide⟩ 24 hp)) T128_128
      hfix128_128 hinj128_128 hcardT128_128
      (fun i => conj_mem_of_fixedPoints _ _ (T128_128 i) (hfix128_128 i) _)
      ⟨128, by decide⟩ ⟨128, by decide⟩ _
      (Q2.validAt ⟨128, by decide⟩ (Q2.listedAt ⟨128, by decide⟩
        (alnCheck_rep ⟨128, by decide⟩ hj hq).1))
      (colE2 ⟨128, by decide⟩ 24 hp) Q2.T128_128_2 Q2.hfix128_128_2 Q2.hinj128_128_2
      Q2.hcardT128_128_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T128_128_2 i) (Q2.hfix128_128_2 i) _)
      colCert_128_128_24.hD ?_).symm
  rw [alnId_128 j hj]


theorem leaf_129_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T129_3
      hfix129_3 hinj129_3 hcardT129_3
      (fun i => conj_mem_of_fixedPoints _ _ (T129_3 i) (hfix129_3 i) _)
      ⟨129, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T129_3_2 Q2.hfix129_3_2 Q2.hinj129_3_2
      Q2.hcardT129_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_3_2 i) (Q2.hfix129_3_2 i) _)
      colCert_129_3_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T129_3
      hfix129_3 hinj129_3 hcardT129_3
      (fun i => conj_mem_of_fixedPoints _ _ (T129_3 i) (hfix129_3 i) _)
      ⟨129, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T129_3_2 Q2.hfix129_3_2 Q2.hinj129_3_2
      Q2.hcardT129_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_3_2 i) (Q2.hfix129_3_2 i) _)
      colCert_129_3_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T129_3
      hfix129_3 hinj129_3 hcardT129_3
      (fun i => conj_mem_of_fixedPoints _ _ (T129_3 i) (hfix129_3 i) _)
      ⟨129, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T129_3_2 Q2.hfix129_3_2 Q2.hinj129_3_2
      Q2.hcardT129_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_3_2 i) (Q2.hfix129_3_2 i) _)
      colCert_129_3_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T129_3
      hfix129_3 hinj129_3 hcardT129_3
      (fun i => conj_mem_of_fixedPoints _ _ (T129_3 i) (hfix129_3 i) _)
      ⟨129, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T129_3_2 Q2.hfix129_3_2 Q2.hinj129_3_2
      Q2.hcardT129_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_3_2 i) (Q2.hfix129_3_2 i) _)
      colCert_129_3_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T129_3
      hfix129_3 hinj129_3 hcardT129_3
      (fun i => conj_mem_of_fixedPoints _ _ (T129_3 i) (hfix129_3 i) _)
      ⟨129, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T129_3_2 Q2.hfix129_3_2 Q2.hinj129_3_2
      Q2.hcardT129_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_3_2 i) (Q2.hfix129_3_2 i) _)
      colCert_129_3_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T129_10
      hfix129_10 hinj129_10 hcardT129_10
      (fun i => conj_mem_of_fixedPoints _ _ (T129_10 i) (hfix129_10 i) _)
      ⟨129, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T129_10_2 Q2.hfix129_10_2 Q2.hinj129_10_2
      Q2.hcardT129_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_10_2 i) (Q2.hfix129_10_2 i) _)
      colCert_129_10_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T129_10
      hfix129_10 hinj129_10 hcardT129_10
      (fun i => conj_mem_of_fixedPoints _ _ (T129_10 i) (hfix129_10 i) _)
      ⟨129, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T129_10_2 Q2.hfix129_10_2 Q2.hinj129_10_2
      Q2.hcardT129_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_10_2 i) (Q2.hfix129_10_2 i) _)
      colCert_129_10_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T129_10
      hfix129_10 hinj129_10 hcardT129_10
      (fun i => conj_mem_of_fixedPoints _ _ (T129_10 i) (hfix129_10 i) _)
      ⟨129, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T129_10_2 Q2.hfix129_10_2 Q2.hinj129_10_2
      Q2.hcardT129_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_10_2 i) (Q2.hfix129_10_2 i) _)
      colCert_129_10_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T129_10
      hfix129_10 hinj129_10 hcardT129_10
      (fun i => conj_mem_of_fixedPoints _ _ (T129_10 i) (hfix129_10 i) _)
      ⟨129, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T129_10_2 Q2.hfix129_10_2 Q2.hinj129_10_2
      Q2.hcardT129_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_10_2 i) (Q2.hfix129_10_2 i) _)
      colCert_129_10_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T129_10
      hfix129_10 hinj129_10 hcardT129_10
      (fun i => conj_mem_of_fixedPoints _ _ (T129_10 i) (hfix129_10 i) _)
      ⟨129, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T129_10_2 Q2.hfix129_10_2 Q2.hinj129_10_2
      Q2.hcardT129_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_10_2 i) (Q2.hfix129_10_2 i) _)
      colCert_129_10_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T129_12
      hfix129_12 hinj129_12 hcardT129_12
      (fun i => conj_mem_of_fixedPoints _ _ (T129_12 i) (hfix129_12 i) _)
      ⟨129, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T129_12_2 Q2.hfix129_12_2 Q2.hinj129_12_2
      Q2.hcardT129_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_12_2 i) (Q2.hfix129_12_2 i) _)
      colCert_129_12_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T129_12
      hfix129_12 hinj129_12 hcardT129_12
      (fun i => conj_mem_of_fixedPoints _ _ (T129_12 i) (hfix129_12 i) _)
      ⟨129, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T129_12_2 Q2.hfix129_12_2 Q2.hinj129_12_2
      Q2.hcardT129_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_12_2 i) (Q2.hfix129_12_2 i) _)
      colCert_129_12_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T129_12
      hfix129_12 hinj129_12 hcardT129_12
      (fun i => conj_mem_of_fixedPoints _ _ (T129_12 i) (hfix129_12 i) _)
      ⟨129, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T129_12_2 Q2.hfix129_12_2 Q2.hinj129_12_2
      Q2.hcardT129_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_12_2 i) (Q2.hfix129_12_2 i) _)
      colCert_129_12_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T129_12
      hfix129_12 hinj129_12 hcardT129_12
      (fun i => conj_mem_of_fixedPoints _ _ (T129_12 i) (hfix129_12 i) _)
      ⟨129, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T129_12_2 Q2.hfix129_12_2 Q2.hinj129_12_2
      Q2.hcardT129_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_12_2 i) (Q2.hfix129_12_2 i) _)
      colCert_129_12_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T129_12
      hfix129_12 hinj129_12 hcardT129_12
      (fun i => conj_mem_of_fixedPoints _ _ (T129_12 i) (hfix129_12 i) _)
      ⟨129, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T129_12_2 Q2.hfix129_12_2 Q2.hinj129_12_2
      Q2.hcardT129_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_12_2 i) (Q2.hfix129_12_2 i) _)
      colCert_129_12_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T129_21
      hfix129_21 hinj129_21 hcardT129_21
      (fun i => conj_mem_of_fixedPoints _ _ (T129_21 i) (hfix129_21 i) _)
      ⟨129, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T129_21_2 Q2.hfix129_21_2 Q2.hinj129_21_2
      Q2.hcardT129_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_21_2 i) (Q2.hfix129_21_2 i) _)
      colCert_129_21_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T129_21
      hfix129_21 hinj129_21 hcardT129_21
      (fun i => conj_mem_of_fixedPoints _ _ (T129_21 i) (hfix129_21 i) _)
      ⟨129, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T129_21_2 Q2.hfix129_21_2 Q2.hinj129_21_2
      Q2.hcardT129_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_21_2 i) (Q2.hfix129_21_2 i) _)
      colCert_129_21_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T129_21
      hfix129_21 hinj129_21 hcardT129_21
      (fun i => conj_mem_of_fixedPoints _ _ (T129_21 i) (hfix129_21 i) _)
      ⟨129, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T129_21_2 Q2.hfix129_21_2 Q2.hinj129_21_2
      Q2.hcardT129_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_21_2 i) (Q2.hfix129_21_2 i) _)
      colCert_129_21_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T129_21
      hfix129_21 hinj129_21 hcardT129_21
      (fun i => conj_mem_of_fixedPoints _ _ (T129_21 i) (hfix129_21 i) _)
      ⟨129, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T129_21_2 Q2.hfix129_21_2 Q2.hinj129_21_2
      Q2.hcardT129_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_21_2 i) (Q2.hfix129_21_2 i) _)
      colCert_129_21_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T129_21
      hfix129_21 hinj129_21 hcardT129_21
      (fun i => conj_mem_of_fixedPoints _ _ (T129_21 i) (hfix129_21 i) _)
      ⟨129, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T129_21_2 Q2.hfix129_21_2 Q2.hinj129_21_2
      Q2.hcardT129_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_21_2 i) (Q2.hfix129_21_2 i) _)
      colCert_129_21_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T129_21
      hfix129_21 hinj129_21 hcardT129_21
      (fun i => conj_mem_of_fixedPoints _ _ (T129_21 i) (hfix129_21 i) _)
      ⟨129, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T129_21_2 Q2.hfix129_21_2 Q2.hinj129_21_2
      Q2.hcardT129_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_21_2 i) (Q2.hfix129_21_2 i) _)
      colCert_129_21_5.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T129_21
      hfix129_21 hinj129_21 hcardT129_21
      (fun i => conj_mem_of_fixedPoints _ _ (T129_21 i) (hfix129_21 i) _)
      ⟨129, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T129_21_2 Q2.hfix129_21_2 Q2.hinj129_21_2
      Q2.hcardT129_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_21_2 i) (Q2.hfix129_21_2 i) _)
      colCert_129_21_10.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T129_21
      hfix129_21 hinj129_21 hcardT129_21
      (fun i => conj_mem_of_fixedPoints _ _ (T129_21 i) (hfix129_21 i) _)
      ⟨129, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T129_21_2 Q2.hfix129_21_2 Q2.hinj129_21_2
      Q2.hcardT129_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_21_2 i) (Q2.hfix129_21_2 i) _)
      colCert_129_21_15.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T129_21
      hfix129_21 hinj129_21 hcardT129_21
      (fun i => conj_mem_of_fixedPoints _ _ (T129_21 i) (hfix129_21 i) _)
      ⟨129, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T129_21_2 Q2.hfix129_21_2 Q2.hinj129_21_2
      Q2.hcardT129_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_21_2 i) (Q2.hfix129_21_2 i) _)
      colCert_129_21_20.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T129_29
      hfix129_29 hinj129_29 hcardT129_29
      (fun i => conj_mem_of_fixedPoints _ _ (T129_29 i) (hfix129_29 i) _)
      ⟨129, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T129_29_2 Q2.hfix129_29_2 Q2.hinj129_29_2
      Q2.hcardT129_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_29_2 i) (Q2.hfix129_29_2 i) _)
      colCert_129_29_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T129_29
      hfix129_29 hinj129_29 hcardT129_29
      (fun i => conj_mem_of_fixedPoints _ _ (T129_29 i) (hfix129_29 i) _)
      ⟨129, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T129_29_2 Q2.hfix129_29_2 Q2.hinj129_29_2
      Q2.hcardT129_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_29_2 i) (Q2.hfix129_29_2 i) _)
      colCert_129_29_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T129_29
      hfix129_29 hinj129_29 hcardT129_29
      (fun i => conj_mem_of_fixedPoints _ _ (T129_29 i) (hfix129_29 i) _)
      ⟨129, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T129_29_2 Q2.hfix129_29_2 Q2.hinj129_29_2
      Q2.hcardT129_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_29_2 i) (Q2.hfix129_29_2 i) _)
      colCert_129_29_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T129_29
      hfix129_29 hinj129_29 hcardT129_29
      (fun i => conj_mem_of_fixedPoints _ _ (T129_29 i) (hfix129_29 i) _)
      ⟨129, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T129_29_2 Q2.hfix129_29_2 Q2.hinj129_29_2
      Q2.hcardT129_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_29_2 i) (Q2.hfix129_29_2 i) _)
      colCert_129_29_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T129_29
      hfix129_29 hinj129_29 hcardT129_29
      (fun i => conj_mem_of_fixedPoints _ _ (T129_29 i) (hfix129_29 i) _)
      ⟨129, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T129_29_2 Q2.hfix129_29_2 Q2.hinj129_29_2
      Q2.hcardT129_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_29_2 i) (Q2.hfix129_29_2 i) _)
      colCert_129_29_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T129_29
      hfix129_29 hinj129_29 hcardT129_29
      (fun i => conj_mem_of_fixedPoints _ _ (T129_29 i) (hfix129_29 i) _)
      ⟨129, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T129_29_2 Q2.hfix129_29_2 Q2.hinj129_29_2
      Q2.hcardT129_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_29_2 i) (Q2.hfix129_29_2 i) _)
      colCert_129_29_5.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T129_29
      hfix129_29 hinj129_29 hcardT129_29
      (fun i => conj_mem_of_fixedPoints _ _ (T129_29 i) (hfix129_29 i) _)
      ⟨129, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T129_29_2 Q2.hfix129_29_2 Q2.hinj129_29_2
      Q2.hcardT129_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_29_2 i) (Q2.hfix129_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T129_29 = colFn colCertDiv_129_29_10.D1 (m := 5) from colCertDiv_129_29_10.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 10 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T129_29_2 = colFn colCertDiv_129_29_10.D2 (m := 5) from colCertDiv_129_29_10.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_29_10_match


theorem leaf_129_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T129_29
      hfix129_29 hinj129_29 hcardT129_29
      (fun i => conj_mem_of_fixedPoints _ _ (T129_29 i) (hfix129_29 i) _)
      ⟨129, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T129_29_2 Q2.hfix129_29_2 Q2.hinj129_29_2
      Q2.hcardT129_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_29_2 i) (Q2.hfix129_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T129_29 = colFn colCertDiv_129_29_15.D1 (m := 5) from colCertDiv_129_29_15.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 15 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T129_29_2 = colFn colCertDiv_129_29_15.D2 (m := 5) from colCertDiv_129_29_15.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_29_15_match


theorem leaf_129_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T129_29
      hfix129_29 hinj129_29 hcardT129_29
      (fun i => conj_mem_of_fixedPoints _ _ (T129_29 i) (hfix129_29 i) _)
      ⟨129, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T129_29_2 Q2.hfix129_29_2 Q2.hinj129_29_2
      Q2.hcardT129_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_29_2 i) (Q2.hfix129_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T129_29 = colFn colCertDiv_129_29_20.D1 (m := 5) from colCertDiv_129_29_20.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 20 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T129_29_2 = colFn colCertDiv_129_29_20.D2 (m := 5) from colCertDiv_129_29_20.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_29_20_match


theorem leaf_129_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T129_35
      hfix129_35 hinj129_35 hcardT129_35
      (fun i => conj_mem_of_fixedPoints _ _ (T129_35 i) (hfix129_35 i) _)
      ⟨129, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T129_35_2 Q2.hfix129_35_2 Q2.hinj129_35_2
      Q2.hcardT129_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_35_2 i) (Q2.hfix129_35_2 i) _)
      colCert_129_35_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T129_35
      hfix129_35 hinj129_35 hcardT129_35
      (fun i => conj_mem_of_fixedPoints _ _ (T129_35 i) (hfix129_35 i) _)
      ⟨129, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T129_35_2 Q2.hfix129_35_2 Q2.hinj129_35_2
      Q2.hcardT129_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_35_2 i) (Q2.hfix129_35_2 i) _)
      colCert_129_35_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T129_35
      hfix129_35 hinj129_35 hcardT129_35
      (fun i => conj_mem_of_fixedPoints _ _ (T129_35 i) (hfix129_35 i) _)
      ⟨129, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T129_35_2 Q2.hfix129_35_2 Q2.hinj129_35_2
      Q2.hcardT129_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_35_2 i) (Q2.hfix129_35_2 i) _)
      colCert_129_35_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T129_35
      hfix129_35 hinj129_35 hcardT129_35
      (fun i => conj_mem_of_fixedPoints _ _ (T129_35 i) (hfix129_35 i) _)
      ⟨129, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T129_35_2 Q2.hfix129_35_2 Q2.hinj129_35_2
      Q2.hcardT129_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_35_2 i) (Q2.hfix129_35_2 i) _)
      colCert_129_35_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T129_35
      hfix129_35 hinj129_35 hcardT129_35
      (fun i => conj_mem_of_fixedPoints _ _ (T129_35 i) (hfix129_35 i) _)
      ⟨129, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T129_35_2 Q2.hfix129_35_2 Q2.hinj129_35_2
      Q2.hcardT129_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_35_2 i) (Q2.hfix129_35_2 i) _)
      colCert_129_35_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T129_35
      hfix129_35 hinj129_35 hcardT129_35
      (fun i => conj_mem_of_fixedPoints _ _ (T129_35 i) (hfix129_35 i) _)
      ⟨129, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T129_35_2 Q2.hfix129_35_2 Q2.hinj129_35_2
      Q2.hcardT129_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_35_2 i) (Q2.hfix129_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T129_35 = colFn colCertDiv_129_35_5.D1 (m := 5) from colCertDiv_129_35_5.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 5 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T129_35_2 = colFn colCertDiv_129_35_5.D2 (m := 5) from colCertDiv_129_35_5.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_35_5_match


theorem leaf_129_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T129_35
      hfix129_35 hinj129_35 hcardT129_35
      (fun i => conj_mem_of_fixedPoints _ _ (T129_35 i) (hfix129_35 i) _)
      ⟨129, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T129_35_2 Q2.hfix129_35_2 Q2.hinj129_35_2
      Q2.hcardT129_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_35_2 i) (Q2.hfix129_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T129_35 = colFn colCertDiv_129_35_10.D1 (m := 5) from colCertDiv_129_35_10.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 10 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T129_35_2 = colFn colCertDiv_129_35_10.D2 (m := 5) from colCertDiv_129_35_10.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_35_10_match


theorem leaf_129_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T129_35
      hfix129_35 hinj129_35 hcardT129_35
      (fun i => conj_mem_of_fixedPoints _ _ (T129_35 i) (hfix129_35 i) _)
      ⟨129, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T129_35_2 Q2.hfix129_35_2 Q2.hinj129_35_2
      Q2.hcardT129_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_35_2 i) (Q2.hfix129_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T129_35 = colFn colCertDiv_129_35_15.D1 (m := 5) from colCertDiv_129_35_15.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 15 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T129_35_2 = colFn colCertDiv_129_35_15.D2 (m := 5) from colCertDiv_129_35_15.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_35_15_match


theorem leaf_129_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T129_35
      hfix129_35 hinj129_35 hcardT129_35
      (fun i => conj_mem_of_fixedPoints _ _ (T129_35 i) (hfix129_35 i) _)
      ⟨129, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T129_35_2 Q2.hfix129_35_2 Q2.hinj129_35_2
      Q2.hcardT129_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_35_2 i) (Q2.hfix129_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T129_35 = colFn colCertDiv_129_35_20.D1 (m := 5) from colCertDiv_129_35_20.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 20 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T129_35_2 = colFn colCertDiv_129_35_20.D2 (m := 5) from colCertDiv_129_35_20.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_35_20_match


theorem leaf_129_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T129_42
      hfix129_42 hinj129_42 hcardT129_42
      (fun i => conj_mem_of_fixedPoints _ _ (T129_42 i) (hfix129_42 i) _)
      ⟨129, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T129_42_2 Q2.hfix129_42_2 Q2.hinj129_42_2
      Q2.hcardT129_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_42_2 i) (Q2.hfix129_42_2 i) _)
      colCert_129_42_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T129_42
      hfix129_42 hinj129_42 hcardT129_42
      (fun i => conj_mem_of_fixedPoints _ _ (T129_42 i) (hfix129_42 i) _)
      ⟨129, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T129_42_2 Q2.hfix129_42_2 Q2.hinj129_42_2
      Q2.hcardT129_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_42_2 i) (Q2.hfix129_42_2 i) _)
      colCert_129_42_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T129_42
      hfix129_42 hinj129_42 hcardT129_42
      (fun i => conj_mem_of_fixedPoints _ _ (T129_42 i) (hfix129_42 i) _)
      ⟨129, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T129_42_2 Q2.hfix129_42_2 Q2.hinj129_42_2
      Q2.hcardT129_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_42_2 i) (Q2.hfix129_42_2 i) _)
      colCert_129_42_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T129_42
      hfix129_42 hinj129_42 hcardT129_42
      (fun i => conj_mem_of_fixedPoints _ _ (T129_42 i) (hfix129_42 i) _)
      ⟨129, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T129_42_2 Q2.hfix129_42_2 Q2.hinj129_42_2
      Q2.hcardT129_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_42_2 i) (Q2.hfix129_42_2 i) _)
      colCert_129_42_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T129_42
      hfix129_42 hinj129_42 hcardT129_42
      (fun i => conj_mem_of_fixedPoints _ _ (T129_42 i) (hfix129_42 i) _)
      ⟨129, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T129_42_2 Q2.hfix129_42_2 Q2.hinj129_42_2
      Q2.hcardT129_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_42_2 i) (Q2.hfix129_42_2 i) _)
      colCert_129_42_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T129_42
      hfix129_42 hinj129_42 hcardT129_42
      (fun i => conj_mem_of_fixedPoints _ _ (T129_42 i) (hfix129_42 i) _)
      ⟨129, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T129_42_2 Q2.hfix129_42_2 Q2.hinj129_42_2
      Q2.hcardT129_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_42_2 i) (Q2.hfix129_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T129_42 = colFn colCertDiv_129_42_5.D1 (m := 5) from colCertDiv_129_42_5.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T129_42_2 = colFn colCertDiv_129_42_5.D2 (m := 5) from colCertDiv_129_42_5.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_42_5_match


theorem leaf_129_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T129_42
      hfix129_42 hinj129_42 hcardT129_42
      (fun i => conj_mem_of_fixedPoints _ _ (T129_42 i) (hfix129_42 i) _)
      ⟨129, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T129_42_2 Q2.hfix129_42_2 Q2.hinj129_42_2
      Q2.hcardT129_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_42_2 i) (Q2.hfix129_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T129_42 = colFn colCertDiv_129_42_10.D1 (m := 5) from colCertDiv_129_42_10.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T129_42_2 = colFn colCertDiv_129_42_10.D2 (m := 5) from colCertDiv_129_42_10.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_42_10_match


theorem leaf_129_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T129_42
      hfix129_42 hinj129_42 hcardT129_42
      (fun i => conj_mem_of_fixedPoints _ _ (T129_42 i) (hfix129_42 i) _)
      ⟨129, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T129_42_2 Q2.hfix129_42_2 Q2.hinj129_42_2
      Q2.hcardT129_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_42_2 i) (Q2.hfix129_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T129_42 = colFn colCertDiv_129_42_15.D1 (m := 5) from colCertDiv_129_42_15.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T129_42_2 = colFn colCertDiv_129_42_15.D2 (m := 5) from colCertDiv_129_42_15.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_42_15_match


theorem leaf_129_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T129_42
      hfix129_42 hinj129_42 hcardT129_42
      (fun i => conj_mem_of_fixedPoints _ _ (T129_42 i) (hfix129_42 i) _)
      ⟨129, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T129_42_2 Q2.hfix129_42_2 Q2.hinj129_42_2
      Q2.hcardT129_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_42_2 i) (Q2.hfix129_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T129_42 = colFn colCertDiv_129_42_20.D1 (m := 5) from colCertDiv_129_42_20.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T129_42_2 = colFn colCertDiv_129_42_20.D2 (m := 5) from colCertDiv_129_42_20.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_42_20_match


theorem leaf_129_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T129_43
      hfix129_43 hinj129_43 hcardT129_43
      (fun i => conj_mem_of_fixedPoints _ _ (T129_43 i) (hfix129_43 i) _)
      ⟨129, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T129_43_2 Q2.hfix129_43_2 Q2.hinj129_43_2
      Q2.hcardT129_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_43_2 i) (Q2.hfix129_43_2 i) _)
      colCert_129_43_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T129_43
      hfix129_43 hinj129_43 hcardT129_43
      (fun i => conj_mem_of_fixedPoints _ _ (T129_43 i) (hfix129_43 i) _)
      ⟨129, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T129_43_2 Q2.hfix129_43_2 Q2.hinj129_43_2
      Q2.hcardT129_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_43_2 i) (Q2.hfix129_43_2 i) _)
      colCert_129_43_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T129_43
      hfix129_43 hinj129_43 hcardT129_43
      (fun i => conj_mem_of_fixedPoints _ _ (T129_43 i) (hfix129_43 i) _)
      ⟨129, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T129_43_2 Q2.hfix129_43_2 Q2.hinj129_43_2
      Q2.hcardT129_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_43_2 i) (Q2.hfix129_43_2 i) _)
      colCert_129_43_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T129_43
      hfix129_43 hinj129_43 hcardT129_43
      (fun i => conj_mem_of_fixedPoints _ _ (T129_43 i) (hfix129_43 i) _)
      ⟨129, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T129_43_2 Q2.hfix129_43_2 Q2.hinj129_43_2
      Q2.hcardT129_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_43_2 i) (Q2.hfix129_43_2 i) _)
      colCert_129_43_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T129_43
      hfix129_43 hinj129_43 hcardT129_43
      (fun i => conj_mem_of_fixedPoints _ _ (T129_43 i) (hfix129_43 i) _)
      ⟨129, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T129_43_2 Q2.hfix129_43_2 Q2.hinj129_43_2
      Q2.hcardT129_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_43_2 i) (Q2.hfix129_43_2 i) _)
      colCert_129_43_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T129_43
      hfix129_43 hinj129_43 hcardT129_43
      (fun i => conj_mem_of_fixedPoints _ _ (T129_43 i) (hfix129_43 i) _)
      ⟨129, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T129_43_2 Q2.hfix129_43_2 Q2.hinj129_43_2
      Q2.hcardT129_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_43_2 i) (Q2.hfix129_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T129_43 = colFn colCertDiv_129_43_5.D1 (m := 5) from colCertDiv_129_43_5.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T129_43_2 = colFn colCertDiv_129_43_5.D2 (m := 5) from colCertDiv_129_43_5.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_43_5_match


theorem leaf_129_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T129_43
      hfix129_43 hinj129_43 hcardT129_43
      (fun i => conj_mem_of_fixedPoints _ _ (T129_43 i) (hfix129_43 i) _)
      ⟨129, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T129_43_2 Q2.hfix129_43_2 Q2.hinj129_43_2
      Q2.hcardT129_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_43_2 i) (Q2.hfix129_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T129_43 = colFn colCertDiv_129_43_10.D1 (m := 5) from colCertDiv_129_43_10.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T129_43_2 = colFn colCertDiv_129_43_10.D2 (m := 5) from colCertDiv_129_43_10.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_43_10_match


theorem leaf_129_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T129_43
      hfix129_43 hinj129_43 hcardT129_43
      (fun i => conj_mem_of_fixedPoints _ _ (T129_43 i) (hfix129_43 i) _)
      ⟨129, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T129_43_2 Q2.hfix129_43_2 Q2.hinj129_43_2
      Q2.hcardT129_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_43_2 i) (Q2.hfix129_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T129_43 = colFn colCertDiv_129_43_15.D1 (m := 5) from colCertDiv_129_43_15.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T129_43_2 = colFn colCertDiv_129_43_15.D2 (m := 5) from colCertDiv_129_43_15.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_43_15_match


theorem leaf_129_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T129_43
      hfix129_43 hinj129_43 hcardT129_43
      (fun i => conj_mem_of_fixedPoints _ _ (T129_43 i) (hfix129_43 i) _)
      ⟨129, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T129_43_2 Q2.hfix129_43_2 Q2.hinj129_43_2
      Q2.hcardT129_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_43_2 i) (Q2.hfix129_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T129_43 = colFn colCertDiv_129_43_20.D1 (m := 5) from colCertDiv_129_43_20.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T129_43_2 = colFn colCertDiv_129_43_20.D2 (m := 5) from colCertDiv_129_43_20.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_43_20_match


theorem leaf_129_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T129_51
      hfix129_51 hinj129_51 hcardT129_51
      (fun i => conj_mem_of_fixedPoints _ _ (T129_51 i) (hfix129_51 i) _)
      ⟨129, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T129_51_2 Q2.hfix129_51_2 Q2.hinj129_51_2
      Q2.hcardT129_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_51_2 i) (Q2.hfix129_51_2 i) _)
      colCert_129_51_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T129_51
      hfix129_51 hinj129_51 hcardT129_51
      (fun i => conj_mem_of_fixedPoints _ _ (T129_51 i) (hfix129_51 i) _)
      ⟨129, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T129_51_2 Q2.hfix129_51_2 Q2.hinj129_51_2
      Q2.hcardT129_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_51_2 i) (Q2.hfix129_51_2 i) _)
      colCert_129_51_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T129_51
      hfix129_51 hinj129_51 hcardT129_51
      (fun i => conj_mem_of_fixedPoints _ _ (T129_51 i) (hfix129_51 i) _)
      ⟨129, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T129_51_2 Q2.hfix129_51_2 Q2.hinj129_51_2
      Q2.hcardT129_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_51_2 i) (Q2.hfix129_51_2 i) _)
      colCert_129_51_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T129_51
      hfix129_51 hinj129_51 hcardT129_51
      (fun i => conj_mem_of_fixedPoints _ _ (T129_51 i) (hfix129_51 i) _)
      ⟨129, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T129_51_2 Q2.hfix129_51_2 Q2.hinj129_51_2
      Q2.hcardT129_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_51_2 i) (Q2.hfix129_51_2 i) _)
      colCert_129_51_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T129_51
      hfix129_51 hinj129_51 hcardT129_51
      (fun i => conj_mem_of_fixedPoints _ _ (T129_51 i) (hfix129_51 i) _)
      ⟨129, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T129_51_2 Q2.hfix129_51_2 Q2.hinj129_51_2
      Q2.hcardT129_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_51_2 i) (Q2.hfix129_51_2 i) _)
      colCert_129_51_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T129_51
      hfix129_51 hinj129_51 hcardT129_51
      (fun i => conj_mem_of_fixedPoints _ _ (T129_51 i) (hfix129_51 i) _)
      ⟨129, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T129_51_2 Q2.hfix129_51_2 Q2.hinj129_51_2
      Q2.hcardT129_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_51_2 i) (Q2.hfix129_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T129_51 = colFn colCertDiv_129_51_5.D1 (m := 5) from colCertDiv_129_51_5.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 5 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T129_51_2 = colFn colCertDiv_129_51_5.D2 (m := 5) from colCertDiv_129_51_5.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_51_5_match


theorem leaf_129_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T129_51
      hfix129_51 hinj129_51 hcardT129_51
      (fun i => conj_mem_of_fixedPoints _ _ (T129_51 i) (hfix129_51 i) _)
      ⟨129, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T129_51_2 Q2.hfix129_51_2 Q2.hinj129_51_2
      Q2.hcardT129_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_51_2 i) (Q2.hfix129_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T129_51 = colFn colCertDiv_129_51_10.D1 (m := 5) from colCertDiv_129_51_10.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 10 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T129_51_2 = colFn colCertDiv_129_51_10.D2 (m := 5) from colCertDiv_129_51_10.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_51_10_match


theorem leaf_129_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T129_51
      hfix129_51 hinj129_51 hcardT129_51
      (fun i => conj_mem_of_fixedPoints _ _ (T129_51 i) (hfix129_51 i) _)
      ⟨129, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T129_51_2 Q2.hfix129_51_2 Q2.hinj129_51_2
      Q2.hcardT129_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_51_2 i) (Q2.hfix129_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T129_51 = colFn colCertDiv_129_51_15.D1 (m := 5) from colCertDiv_129_51_15.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 15 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T129_51_2 = colFn colCertDiv_129_51_15.D2 (m := 5) from colCertDiv_129_51_15.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_51_15_match


theorem leaf_129_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T129_51
      hfix129_51 hinj129_51 hcardT129_51
      (fun i => conj_mem_of_fixedPoints _ _ (T129_51 i) (hfix129_51 i) _)
      ⟨129, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T129_51_2 Q2.hfix129_51_2 Q2.hinj129_51_2
      Q2.hcardT129_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_51_2 i) (Q2.hfix129_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T129_51 = colFn colCertDiv_129_51_20.D1 (m := 5) from colCertDiv_129_51_20.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 20 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T129_51_2 = colFn colCertDiv_129_51_20.D2 (m := 5) from colCertDiv_129_51_20.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_51_20_match


theorem leaf_129_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T129_53
      hfix129_53 hinj129_53 hcardT129_53
      (fun i => conj_mem_of_fixedPoints _ _ (T129_53 i) (hfix129_53 i) _)
      ⟨129, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T129_53_2 Q2.hfix129_53_2 Q2.hinj129_53_2
      Q2.hcardT129_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_53_2 i) (Q2.hfix129_53_2 i) _)
      colCert_129_53_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T129_53
      hfix129_53 hinj129_53 hcardT129_53
      (fun i => conj_mem_of_fixedPoints _ _ (T129_53 i) (hfix129_53 i) _)
      ⟨129, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T129_53_2 Q2.hfix129_53_2 Q2.hinj129_53_2
      Q2.hcardT129_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_53_2 i) (Q2.hfix129_53_2 i) _)
      colCert_129_53_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T129_53
      hfix129_53 hinj129_53 hcardT129_53
      (fun i => conj_mem_of_fixedPoints _ _ (T129_53 i) (hfix129_53 i) _)
      ⟨129, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T129_53_2 Q2.hfix129_53_2 Q2.hinj129_53_2
      Q2.hcardT129_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_53_2 i) (Q2.hfix129_53_2 i) _)
      colCert_129_53_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T129_53
      hfix129_53 hinj129_53 hcardT129_53
      (fun i => conj_mem_of_fixedPoints _ _ (T129_53 i) (hfix129_53 i) _)
      ⟨129, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T129_53_2 Q2.hfix129_53_2 Q2.hinj129_53_2
      Q2.hcardT129_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_53_2 i) (Q2.hfix129_53_2 i) _)
      colCert_129_53_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T129_53
      hfix129_53 hinj129_53 hcardT129_53
      (fun i => conj_mem_of_fixedPoints _ _ (T129_53 i) (hfix129_53 i) _)
      ⟨129, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T129_53_2 Q2.hfix129_53_2 Q2.hinj129_53_2
      Q2.hcardT129_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_53_2 i) (Q2.hfix129_53_2 i) _)
      colCert_129_53_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T129_53
      hfix129_53 hinj129_53 hcardT129_53
      (fun i => conj_mem_of_fixedPoints _ _ (T129_53 i) (hfix129_53 i) _)
      ⟨129, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T129_53_2 Q2.hfix129_53_2 Q2.hinj129_53_2
      Q2.hcardT129_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_53_2 i) (Q2.hfix129_53_2 i) _)
      colCert_129_53_5.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T129_53
      hfix129_53 hinj129_53 hcardT129_53
      (fun i => conj_mem_of_fixedPoints _ _ (T129_53 i) (hfix129_53 i) _)
      ⟨129, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T129_53_2 Q2.hfix129_53_2 Q2.hinj129_53_2
      Q2.hcardT129_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_53_2 i) (Q2.hfix129_53_2 i) _)
      colCert_129_53_10.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T129_53
      hfix129_53 hinj129_53 hcardT129_53
      (fun i => conj_mem_of_fixedPoints _ _ (T129_53 i) (hfix129_53 i) _)
      ⟨129, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T129_53_2 Q2.hfix129_53_2 Q2.hinj129_53_2
      Q2.hcardT129_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_53_2 i) (Q2.hfix129_53_2 i) _)
      colCert_129_53_15.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T129_53
      hfix129_53 hinj129_53 hcardT129_53
      (fun i => conj_mem_of_fixedPoints _ _ (T129_53 i) (hfix129_53 i) _)
      ⟨129, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T129_53_2 Q2.hfix129_53_2 Q2.hinj129_53_2
      Q2.hcardT129_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_53_2 i) (Q2.hfix129_53_2 i) _)
      colCert_129_53_20.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_82_0 (hp : 0 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp)) T129_82
      hfix129_82 hinj129_82 hcardT129_82
      (fun i => conj_mem_of_fixedPoints _ _ (T129_82 i) (hfix129_82 i) _)
      ⟨129, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 0 hp) Q2.T129_82_2 Q2.hfix129_82_2 Q2.hinj129_82_2
      Q2.hcardT129_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_82_2 i) (Q2.hfix129_82_2 i) _)
      colCert_129_82_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_82_1 (hp : 1 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp)) T129_82
      hfix129_82 hinj129_82 hcardT129_82
      (fun i => conj_mem_of_fixedPoints _ _ (T129_82 i) (hfix129_82 i) _)
      ⟨129, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 1 hp) Q2.T129_82_2 Q2.hfix129_82_2 Q2.hinj129_82_2
      Q2.hcardT129_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_82_2 i) (Q2.hfix129_82_2 i) _)
      colCert_129_82_1.hD ?_).symm
  rw [alnId_129 j hj]


end LeanDring.P5Presentation
