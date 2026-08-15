/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C040
import LeanDring.P5.Data.ColCdd.C041
import LeanDring.P5.Data.ColRestCheap.C171
import LeanDring.P5.Data.ColRestCheap.C172
import LeanDring.P5.Data.ColRestCheap.C173
import LeanDring.P5.Data.ColRestCheap.C174
import LeanDring.P5.Data.EntryK.C018
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C049
import LeanDring.P5.Data.SpeciesDiv.C050
import LeanDring.P5.Data.SpeciesDiv.C053

/-! # Stage-5 leaves, chunk 12 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_77_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T77_25
      hfix77_25 hinj77_25 hcardT77_25
      (fun i => conj_mem_of_fixedPoints _ _ (T77_25 i) (hfix77_25 i) _)
      ⟨77, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T77_25_2 Q2.hfix77_25_2 Q2.hinj77_25_2
      Q2.hcardT77_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_25_2 i) (Q2.hfix77_25_2 i) _)
      colCert_77_25_3.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T77_25
      hfix77_25 hinj77_25 hcardT77_25
      (fun i => conj_mem_of_fixedPoints _ _ (T77_25 i) (hfix77_25 i) _)
      ⟨77, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T77_25_2 Q2.hfix77_25_2 Q2.hinj77_25_2
      Q2.hcardT77_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_25_2 i) (Q2.hfix77_25_2 i) _)
      colCert_77_25_4.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T77_25
      hfix77_25 hinj77_25 hcardT77_25
      (fun i => conj_mem_of_fixedPoints _ _ (T77_25 i) (hfix77_25 i) _)
      ⟨77, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T77_25_2 Q2.hfix77_25_2 Q2.hinj77_25_2
      Q2.hcardT77_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_25_2 i) (Q2.hfix77_25_2 i) _)
      colCert_77_25_5.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T77_25
      hfix77_25 hinj77_25 hcardT77_25
      (fun i => conj_mem_of_fixedPoints _ _ (T77_25 i) (hfix77_25 i) _)
      ⟨77, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T77_25_2 Q2.hfix77_25_2 Q2.hinj77_25_2
      Q2.hcardT77_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_25_2 i) (Q2.hfix77_25_2 i) _)
      colCert_77_25_10.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T77_25
      hfix77_25 hinj77_25 hcardT77_25
      (fun i => conj_mem_of_fixedPoints _ _ (T77_25 i) (hfix77_25 i) _)
      ⟨77, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T77_25_2 Q2.hfix77_25_2 Q2.hinj77_25_2
      Q2.hcardT77_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_25_2 i) (Q2.hfix77_25_2 i) _)
      colCert_77_25_15.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T77_25
      hfix77_25 hinj77_25 hcardT77_25
      (fun i => conj_mem_of_fixedPoints _ _ (T77_25 i) (hfix77_25 i) _)
      ⟨77, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T77_25_2 Q2.hfix77_25_2 Q2.hinj77_25_2
      Q2.hcardT77_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_25_2 i) (Q2.hfix77_25_2 i) _)
      colCert_77_25_20.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T77_32
      hfix77_32 hinj77_32 hcardT77_32
      (fun i => conj_mem_of_fixedPoints _ _ (T77_32 i) (hfix77_32 i) _)
      ⟨77, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T77_32_2 Q2.hfix77_32_2 Q2.hinj77_32_2
      Q2.hcardT77_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_32_2 i) (Q2.hfix77_32_2 i) _)
      colCert_77_32_0.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T77_32
      hfix77_32 hinj77_32 hcardT77_32
      (fun i => conj_mem_of_fixedPoints _ _ (T77_32 i) (hfix77_32 i) _)
      ⟨77, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T77_32_2 Q2.hfix77_32_2 Q2.hinj77_32_2
      Q2.hcardT77_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_32_2 i) (Q2.hfix77_32_2 i) _)
      colCert_77_32_1.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T77_32
      hfix77_32 hinj77_32 hcardT77_32
      (fun i => conj_mem_of_fixedPoints _ _ (T77_32 i) (hfix77_32 i) _)
      ⟨77, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T77_32_2 Q2.hfix77_32_2 Q2.hinj77_32_2
      Q2.hcardT77_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_32_2 i) (Q2.hfix77_32_2 i) _)
      colCert_77_32_2.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T77_32
      hfix77_32 hinj77_32 hcardT77_32
      (fun i => conj_mem_of_fixedPoints _ _ (T77_32 i) (hfix77_32 i) _)
      ⟨77, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T77_32_2 Q2.hfix77_32_2 Q2.hinj77_32_2
      Q2.hcardT77_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_32_2 i) (Q2.hfix77_32_2 i) _)
      colCert_77_32_3.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T77_32
      hfix77_32 hinj77_32 hcardT77_32
      (fun i => conj_mem_of_fixedPoints _ _ (T77_32 i) (hfix77_32 i) _)
      ⟨77, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T77_32_2 Q2.hfix77_32_2 Q2.hinj77_32_2
      Q2.hcardT77_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_32_2 i) (Q2.hfix77_32_2 i) _)
      colCert_77_32_4.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T77_32
      hfix77_32 hinj77_32 hcardT77_32
      (fun i => conj_mem_of_fixedPoints _ _ (T77_32 i) (hfix77_32 i) _)
      ⟨77, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T77_32_2 Q2.hfix77_32_2 Q2.hinj77_32_2
      Q2.hcardT77_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_32_2 i) (Q2.hfix77_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T77_32 = colFn colCertDiv_77_32_5.D1 (m := 5) from colCertDiv_77_32_5.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 5 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T77_32_2 = colFn colCertDiv_77_32_5.D2 (m := 5) from colCertDiv_77_32_5.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_32_5_match


theorem leaf_77_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T77_32
      hfix77_32 hinj77_32 hcardT77_32
      (fun i => conj_mem_of_fixedPoints _ _ (T77_32 i) (hfix77_32 i) _)
      ⟨77, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T77_32_2 Q2.hfix77_32_2 Q2.hinj77_32_2
      Q2.hcardT77_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_32_2 i) (Q2.hfix77_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T77_32 = colFn colCertDiv_77_32_10.D1 (m := 5) from colCertDiv_77_32_10.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 10 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T77_32_2 = colFn colCertDiv_77_32_10.D2 (m := 5) from colCertDiv_77_32_10.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_32_10_match


theorem leaf_77_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T77_32
      hfix77_32 hinj77_32 hcardT77_32
      (fun i => conj_mem_of_fixedPoints _ _ (T77_32 i) (hfix77_32 i) _)
      ⟨77, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T77_32_2 Q2.hfix77_32_2 Q2.hinj77_32_2
      Q2.hcardT77_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_32_2 i) (Q2.hfix77_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T77_32 = colFn colCertDiv_77_32_15.D1 (m := 5) from colCertDiv_77_32_15.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 15 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T77_32_2 = colFn colCertDiv_77_32_15.D2 (m := 5) from colCertDiv_77_32_15.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_32_15_match


theorem leaf_77_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T77_32
      hfix77_32 hinj77_32 hcardT77_32
      (fun i => conj_mem_of_fixedPoints _ _ (T77_32 i) (hfix77_32 i) _)
      ⟨77, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T77_32_2 Q2.hfix77_32_2 Q2.hinj77_32_2
      Q2.hcardT77_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_32_2 i) (Q2.hfix77_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T77_32 = colFn colCertDiv_77_32_20.D1 (m := 5) from colCertDiv_77_32_20.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 20 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T77_32_2 = colFn colCertDiv_77_32_20.D2 (m := 5) from colCertDiv_77_32_20.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_32_20_match


theorem leaf_77_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T77_37
      hfix77_37 hinj77_37 hcardT77_37
      (fun i => conj_mem_of_fixedPoints _ _ (T77_37 i) (hfix77_37 i) _)
      ⟨77, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T77_37_2 Q2.hfix77_37_2 Q2.hinj77_37_2
      Q2.hcardT77_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_37_2 i) (Q2.hfix77_37_2 i) _)
      colCert_77_37_0.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T77_37
      hfix77_37 hinj77_37 hcardT77_37
      (fun i => conj_mem_of_fixedPoints _ _ (T77_37 i) (hfix77_37 i) _)
      ⟨77, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T77_37_2 Q2.hfix77_37_2 Q2.hinj77_37_2
      Q2.hcardT77_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_37_2 i) (Q2.hfix77_37_2 i) _)
      colCert_77_37_1.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T77_37
      hfix77_37 hinj77_37 hcardT77_37
      (fun i => conj_mem_of_fixedPoints _ _ (T77_37 i) (hfix77_37 i) _)
      ⟨77, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T77_37_2 Q2.hfix77_37_2 Q2.hinj77_37_2
      Q2.hcardT77_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_37_2 i) (Q2.hfix77_37_2 i) _)
      colCert_77_37_2.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T77_37
      hfix77_37 hinj77_37 hcardT77_37
      (fun i => conj_mem_of_fixedPoints _ _ (T77_37 i) (hfix77_37 i) _)
      ⟨77, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T77_37_2 Q2.hfix77_37_2 Q2.hinj77_37_2
      Q2.hcardT77_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_37_2 i) (Q2.hfix77_37_2 i) _)
      colCert_77_37_3.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T77_37
      hfix77_37 hinj77_37 hcardT77_37
      (fun i => conj_mem_of_fixedPoints _ _ (T77_37 i) (hfix77_37 i) _)
      ⟨77, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T77_37_2 Q2.hfix77_37_2 Q2.hinj77_37_2
      Q2.hcardT77_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_37_2 i) (Q2.hfix77_37_2 i) _)
      colCert_77_37_4.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T77_37
      hfix77_37 hinj77_37 hcardT77_37
      (fun i => conj_mem_of_fixedPoints _ _ (T77_37 i) (hfix77_37 i) _)
      ⟨77, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T77_37_2 Q2.hfix77_37_2 Q2.hinj77_37_2
      Q2.hcardT77_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_37_2 i) (Q2.hfix77_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T77_37 = colFn colCertDiv_77_37_5.D1 (m := 5) from colCertDiv_77_37_5.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T77_37_2 = colFn colCertDiv_77_37_5.D2 (m := 5) from colCertDiv_77_37_5.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_37_5_match


theorem leaf_77_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T77_37
      hfix77_37 hinj77_37 hcardT77_37
      (fun i => conj_mem_of_fixedPoints _ _ (T77_37 i) (hfix77_37 i) _)
      ⟨77, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T77_37_2 Q2.hfix77_37_2 Q2.hinj77_37_2
      Q2.hcardT77_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_37_2 i) (Q2.hfix77_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T77_37 = colFn colCertDiv_77_37_10.D1 (m := 5) from colCertDiv_77_37_10.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T77_37_2 = colFn colCertDiv_77_37_10.D2 (m := 5) from colCertDiv_77_37_10.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_37_10_match


theorem leaf_77_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T77_37
      hfix77_37 hinj77_37 hcardT77_37
      (fun i => conj_mem_of_fixedPoints _ _ (T77_37 i) (hfix77_37 i) _)
      ⟨77, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T77_37_2 Q2.hfix77_37_2 Q2.hinj77_37_2
      Q2.hcardT77_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_37_2 i) (Q2.hfix77_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T77_37 = colFn colCertDiv_77_37_15.D1 (m := 5) from colCertDiv_77_37_15.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T77_37_2 = colFn colCertDiv_77_37_15.D2 (m := 5) from colCertDiv_77_37_15.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_37_15_match


theorem leaf_77_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T77_37
      hfix77_37 hinj77_37 hcardT77_37
      (fun i => conj_mem_of_fixedPoints _ _ (T77_37 i) (hfix77_37 i) _)
      ⟨77, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T77_37_2 Q2.hfix77_37_2 Q2.hinj77_37_2
      Q2.hcardT77_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_37_2 i) (Q2.hfix77_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T77_37 = colFn colCertDiv_77_37_20.D1 (m := 5) from colCertDiv_77_37_20.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T77_37_2 = colFn colCertDiv_77_37_20.D2 (m := 5) from colCertDiv_77_37_20.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_37_20_match


theorem leaf_77_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T77_42
      hfix77_42 hinj77_42 hcardT77_42
      (fun i => conj_mem_of_fixedPoints _ _ (T77_42 i) (hfix77_42 i) _)
      ⟨77, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T77_42_2 Q2.hfix77_42_2 Q2.hinj77_42_2
      Q2.hcardT77_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_42_2 i) (Q2.hfix77_42_2 i) _)
      colCert_77_42_0.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T77_42
      hfix77_42 hinj77_42 hcardT77_42
      (fun i => conj_mem_of_fixedPoints _ _ (T77_42 i) (hfix77_42 i) _)
      ⟨77, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T77_42_2 Q2.hfix77_42_2 Q2.hinj77_42_2
      Q2.hcardT77_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_42_2 i) (Q2.hfix77_42_2 i) _)
      colCert_77_42_1.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T77_42
      hfix77_42 hinj77_42 hcardT77_42
      (fun i => conj_mem_of_fixedPoints _ _ (T77_42 i) (hfix77_42 i) _)
      ⟨77, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T77_42_2 Q2.hfix77_42_2 Q2.hinj77_42_2
      Q2.hcardT77_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_42_2 i) (Q2.hfix77_42_2 i) _)
      colCert_77_42_2.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T77_42
      hfix77_42 hinj77_42 hcardT77_42
      (fun i => conj_mem_of_fixedPoints _ _ (T77_42 i) (hfix77_42 i) _)
      ⟨77, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T77_42_2 Q2.hfix77_42_2 Q2.hinj77_42_2
      Q2.hcardT77_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_42_2 i) (Q2.hfix77_42_2 i) _)
      colCert_77_42_3.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T77_42
      hfix77_42 hinj77_42 hcardT77_42
      (fun i => conj_mem_of_fixedPoints _ _ (T77_42 i) (hfix77_42 i) _)
      ⟨77, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T77_42_2 Q2.hfix77_42_2 Q2.hinj77_42_2
      Q2.hcardT77_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_42_2 i) (Q2.hfix77_42_2 i) _)
      colCert_77_42_4.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T77_42
      hfix77_42 hinj77_42 hcardT77_42
      (fun i => conj_mem_of_fixedPoints _ _ (T77_42 i) (hfix77_42 i) _)
      ⟨77, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T77_42_2 Q2.hfix77_42_2 Q2.hinj77_42_2
      Q2.hcardT77_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_42_2 i) (Q2.hfix77_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T77_42 = colFn colCertDiv_77_42_5.D1 (m := 5) from colCertDiv_77_42_5.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T77_42_2 = colFn colCertDiv_77_42_5.D2 (m := 5) from colCertDiv_77_42_5.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_42_5_match


theorem leaf_77_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T77_42
      hfix77_42 hinj77_42 hcardT77_42
      (fun i => conj_mem_of_fixedPoints _ _ (T77_42 i) (hfix77_42 i) _)
      ⟨77, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T77_42_2 Q2.hfix77_42_2 Q2.hinj77_42_2
      Q2.hcardT77_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_42_2 i) (Q2.hfix77_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T77_42 = colFn colCertDiv_77_42_10.D1 (m := 5) from colCertDiv_77_42_10.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T77_42_2 = colFn colCertDiv_77_42_10.D2 (m := 5) from colCertDiv_77_42_10.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_42_10_match


theorem leaf_77_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T77_42
      hfix77_42 hinj77_42 hcardT77_42
      (fun i => conj_mem_of_fixedPoints _ _ (T77_42 i) (hfix77_42 i) _)
      ⟨77, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T77_42_2 Q2.hfix77_42_2 Q2.hinj77_42_2
      Q2.hcardT77_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_42_2 i) (Q2.hfix77_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T77_42 = colFn colCertDiv_77_42_15.D1 (m := 5) from colCertDiv_77_42_15.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T77_42_2 = colFn colCertDiv_77_42_15.D2 (m := 5) from colCertDiv_77_42_15.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_42_15_match


theorem leaf_77_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T77_42
      hfix77_42 hinj77_42 hcardT77_42
      (fun i => conj_mem_of_fixedPoints _ _ (T77_42 i) (hfix77_42 i) _)
      ⟨77, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T77_42_2 Q2.hfix77_42_2 Q2.hinj77_42_2
      Q2.hcardT77_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_42_2 i) (Q2.hfix77_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T77_42 = colFn colCertDiv_77_42_20.D1 (m := 5) from colCertDiv_77_42_20.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T77_42_2 = colFn colCertDiv_77_42_20.D2 (m := 5) from colCertDiv_77_42_20.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_42_20_match


theorem leaf_77_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T77_47
      hfix77_47 hinj77_47 hcardT77_47
      (fun i => conj_mem_of_fixedPoints _ _ (T77_47 i) (hfix77_47 i) _)
      ⟨77, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T77_47_2 Q2.hfix77_47_2 Q2.hinj77_47_2
      Q2.hcardT77_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_47_2 i) (Q2.hfix77_47_2 i) _)
      colCert_77_47_0.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T77_47
      hfix77_47 hinj77_47 hcardT77_47
      (fun i => conj_mem_of_fixedPoints _ _ (T77_47 i) (hfix77_47 i) _)
      ⟨77, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T77_47_2 Q2.hfix77_47_2 Q2.hinj77_47_2
      Q2.hcardT77_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_47_2 i) (Q2.hfix77_47_2 i) _)
      colCert_77_47_1.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T77_47
      hfix77_47 hinj77_47 hcardT77_47
      (fun i => conj_mem_of_fixedPoints _ _ (T77_47 i) (hfix77_47 i) _)
      ⟨77, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T77_47_2 Q2.hfix77_47_2 Q2.hinj77_47_2
      Q2.hcardT77_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_47_2 i) (Q2.hfix77_47_2 i) _)
      colCert_77_47_2.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T77_47
      hfix77_47 hinj77_47 hcardT77_47
      (fun i => conj_mem_of_fixedPoints _ _ (T77_47 i) (hfix77_47 i) _)
      ⟨77, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T77_47_2 Q2.hfix77_47_2 Q2.hinj77_47_2
      Q2.hcardT77_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_47_2 i) (Q2.hfix77_47_2 i) _)
      colCert_77_47_3.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T77_47
      hfix77_47 hinj77_47 hcardT77_47
      (fun i => conj_mem_of_fixedPoints _ _ (T77_47 i) (hfix77_47 i) _)
      ⟨77, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T77_47_2 Q2.hfix77_47_2 Q2.hinj77_47_2
      Q2.hcardT77_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_47_2 i) (Q2.hfix77_47_2 i) _)
      colCert_77_47_4.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T77_47
      hfix77_47 hinj77_47 hcardT77_47
      (fun i => conj_mem_of_fixedPoints _ _ (T77_47 i) (hfix77_47 i) _)
      ⟨77, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T77_47_2 Q2.hfix77_47_2 Q2.hinj77_47_2
      Q2.hcardT77_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_47_2 i) (Q2.hfix77_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T77_47 = colFn colCertDiv_77_47_5.D1 (m := 5) from colCertDiv_77_47_5.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T77_47_2 = colFn colCertDiv_77_47_5.D2 (m := 5) from colCertDiv_77_47_5.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_47_5_match


theorem leaf_77_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T77_47
      hfix77_47 hinj77_47 hcardT77_47
      (fun i => conj_mem_of_fixedPoints _ _ (T77_47 i) (hfix77_47 i) _)
      ⟨77, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T77_47_2 Q2.hfix77_47_2 Q2.hinj77_47_2
      Q2.hcardT77_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_47_2 i) (Q2.hfix77_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T77_47 = colFn colCertDiv_77_47_10.D1 (m := 5) from colCertDiv_77_47_10.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T77_47_2 = colFn colCertDiv_77_47_10.D2 (m := 5) from colCertDiv_77_47_10.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_47_10_match


theorem leaf_77_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T77_47
      hfix77_47 hinj77_47 hcardT77_47
      (fun i => conj_mem_of_fixedPoints _ _ (T77_47 i) (hfix77_47 i) _)
      ⟨77, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T77_47_2 Q2.hfix77_47_2 Q2.hinj77_47_2
      Q2.hcardT77_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_47_2 i) (Q2.hfix77_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T77_47 = colFn colCertDiv_77_47_15.D1 (m := 5) from colCertDiv_77_47_15.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T77_47_2 = colFn colCertDiv_77_47_15.D2 (m := 5) from colCertDiv_77_47_15.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_47_15_match


theorem leaf_77_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T77_47
      hfix77_47 hinj77_47 hcardT77_47
      (fun i => conj_mem_of_fixedPoints _ _ (T77_47 i) (hfix77_47 i) _)
      ⟨77, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T77_47_2 Q2.hfix77_47_2 Q2.hinj77_47_2
      Q2.hcardT77_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_47_2 i) (Q2.hfix77_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T77_47 = colFn colCertDiv_77_47_20.D1 (m := 5) from colCertDiv_77_47_20.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T77_47_2 = colFn colCertDiv_77_47_20.D2 (m := 5) from colCertDiv_77_47_20.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_47_20_match


theorem leaf_77_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T77_52
      hfix77_52 hinj77_52 hcardT77_52
      (fun i => conj_mem_of_fixedPoints _ _ (T77_52 i) (hfix77_52 i) _)
      ⟨77, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T77_52_2 Q2.hfix77_52_2 Q2.hinj77_52_2
      Q2.hcardT77_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_52_2 i) (Q2.hfix77_52_2 i) _)
      colCert_77_52_0.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T77_52
      hfix77_52 hinj77_52 hcardT77_52
      (fun i => conj_mem_of_fixedPoints _ _ (T77_52 i) (hfix77_52 i) _)
      ⟨77, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T77_52_2 Q2.hfix77_52_2 Q2.hinj77_52_2
      Q2.hcardT77_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_52_2 i) (Q2.hfix77_52_2 i) _)
      colCert_77_52_1.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T77_52
      hfix77_52 hinj77_52 hcardT77_52
      (fun i => conj_mem_of_fixedPoints _ _ (T77_52 i) (hfix77_52 i) _)
      ⟨77, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T77_52_2 Q2.hfix77_52_2 Q2.hinj77_52_2
      Q2.hcardT77_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_52_2 i) (Q2.hfix77_52_2 i) _)
      colCert_77_52_2.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T77_52
      hfix77_52 hinj77_52 hcardT77_52
      (fun i => conj_mem_of_fixedPoints _ _ (T77_52 i) (hfix77_52 i) _)
      ⟨77, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T77_52_2 Q2.hfix77_52_2 Q2.hinj77_52_2
      Q2.hcardT77_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_52_2 i) (Q2.hfix77_52_2 i) _)
      colCert_77_52_3.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T77_52
      hfix77_52 hinj77_52 hcardT77_52
      (fun i => conj_mem_of_fixedPoints _ _ (T77_52 i) (hfix77_52 i) _)
      ⟨77, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T77_52_2 Q2.hfix77_52_2 Q2.hinj77_52_2
      Q2.hcardT77_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_52_2 i) (Q2.hfix77_52_2 i) _)
      colCert_77_52_4.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T77_52
      hfix77_52 hinj77_52 hcardT77_52
      (fun i => conj_mem_of_fixedPoints _ _ (T77_52 i) (hfix77_52 i) _)
      ⟨77, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T77_52_2 Q2.hfix77_52_2 Q2.hinj77_52_2
      Q2.hcardT77_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_52_2 i) (Q2.hfix77_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T77_52 = colFn colCertDiv_77_52_5.D1 (m := 5) from colCertDiv_77_52_5.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T77_52_2 = colFn colCertDiv_77_52_5.D2 (m := 5) from colCertDiv_77_52_5.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_52_5_match


theorem leaf_77_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T77_52
      hfix77_52 hinj77_52 hcardT77_52
      (fun i => conj_mem_of_fixedPoints _ _ (T77_52 i) (hfix77_52 i) _)
      ⟨77, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T77_52_2 Q2.hfix77_52_2 Q2.hinj77_52_2
      Q2.hcardT77_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_52_2 i) (Q2.hfix77_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T77_52 = colFn colCertDiv_77_52_10.D1 (m := 5) from colCertDiv_77_52_10.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T77_52_2 = colFn colCertDiv_77_52_10.D2 (m := 5) from colCertDiv_77_52_10.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_52_10_match


theorem leaf_77_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T77_52
      hfix77_52 hinj77_52 hcardT77_52
      (fun i => conj_mem_of_fixedPoints _ _ (T77_52 i) (hfix77_52 i) _)
      ⟨77, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T77_52_2 Q2.hfix77_52_2 Q2.hinj77_52_2
      Q2.hcardT77_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_52_2 i) (Q2.hfix77_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T77_52 = colFn colCertDiv_77_52_15.D1 (m := 5) from colCertDiv_77_52_15.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T77_52_2 = colFn colCertDiv_77_52_15.D2 (m := 5) from colCertDiv_77_52_15.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_52_15_match


theorem leaf_77_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨77, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T77_52
      hfix77_52 hinj77_52 hcardT77_52
      (fun i => conj_mem_of_fixedPoints _ _ (T77_52 i) (hfix77_52 i) _)
      ⟨77, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T77_52_2 Q2.hfix77_52_2 Q2.hinj77_52_2
      Q2.hcardT77_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_52_2 i) (Q2.hfix77_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨77, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T77_52 = colFn colCertDiv_77_52_20.D1 (m := 5) from colCertDiv_77_52_20.bind1,
    show colData2 (⟨77, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T77_52_2 = colFn colCertDiv_77_52_20.D2 (m := 5) from colCertDiv_77_52_20.bind2]
  rw [alnId_77 j hj]
  exact fastcode_of_div ⟨77, by decide⟩ _ _ _
    ((alnId_77 j hj) ▸ Q2.listedAt (⟨77, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨77, by decide⟩ : Fin 148) hj hq).1) colCertDiv_77_52_20_match


theorem leaf_77_77_0 (hp : 0 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 0 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 0 (transLenTr ⟨77, by decide⟩ 0 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 0 (transLenTr ⟨77, by decide⟩ 0 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 0 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_0.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_1 (hp : 1 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 1 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 1 (transLenTr ⟨77, by decide⟩ 1 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 1 (transLenTr ⟨77, by decide⟩ 1 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 1 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_1.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_2 (hp : 2 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 2 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 2 (transLenTr ⟨77, by decide⟩ 2 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 2 (transLenTr ⟨77, by decide⟩ 2 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 2 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_2.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_3 (hp : 3 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 3 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 3 (transLenTr ⟨77, by decide⟩ 3 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 3 (transLenTr ⟨77, by decide⟩ 3 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 3 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_3.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_4 (hp : 4 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 4 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 4 (transLenTr ⟨77, by decide⟩ 4 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 4 (transLenTr ⟨77, by decide⟩ 4 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 4 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_4.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_5 (hp : 5 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 5 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 5 (transLenTr ⟨77, by decide⟩ 5 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 5 (transLenTr ⟨77, by decide⟩ 5 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 5 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_5.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_6 (hp : 6 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 6 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 6 (transLenTr ⟨77, by decide⟩ 6 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 6 (transLenTr ⟨77, by decide⟩ 6 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 6 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_6.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_7 (hp : 7 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 7 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 7 (transLenTr ⟨77, by decide⟩ 7 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 7 (transLenTr ⟨77, by decide⟩ 7 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 7 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_7.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_8 (hp : 8 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 8 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 8 (transLenTr ⟨77, by decide⟩ 8 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 8 (transLenTr ⟨77, by decide⟩ 8 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 8 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_8.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_9 (hp : 9 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 9 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 9 (transLenTr ⟨77, by decide⟩ 9 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 9 (transLenTr ⟨77, by decide⟩ 9 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 9 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_9.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_10 (hp : 10 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 10 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 10 (transLenTr ⟨77, by decide⟩ 10 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 10 (transLenTr ⟨77, by decide⟩ 10 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 10 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_10.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_11 (hp : 11 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 11 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 11 (transLenTr ⟨77, by decide⟩ 11 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 11 (transLenTr ⟨77, by decide⟩ 11 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 11 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_11.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_12 (hp : 12 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 12 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 12 (transLenTr ⟨77, by decide⟩ 12 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 12 (transLenTr ⟨77, by decide⟩ 12 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 12 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_12.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_13 (hp : 13 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 13 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 13 (transLenTr ⟨77, by decide⟩ 13 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 13 (transLenTr ⟨77, by decide⟩ 13 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 13 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_13.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_14 (hp : 14 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 14 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 14 (transLenTr ⟨77, by decide⟩ 14 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 14 (transLenTr ⟨77, by decide⟩ 14 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 14 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_14.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_15 (hp : 15 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 15 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 15 (transLenTr ⟨77, by decide⟩ 15 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 15 (transLenTr ⟨77, by decide⟩ 15 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 15 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_15.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_16 (hp : 16 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 16 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 16 (transLenTr ⟨77, by decide⟩ 16 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 16 (transLenTr ⟨77, by decide⟩ 16 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 16 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_16.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_17 (hp : 17 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 17 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 17 (transLenTr ⟨77, by decide⟩ 17 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 17 (transLenTr ⟨77, by decide⟩ 17 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 17 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_17.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_18 (hp : 18 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 18 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 18 (transLenTr ⟨77, by decide⟩ 18 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 18 (transLenTr ⟨77, by decide⟩ 18 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 18 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_18.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_19 (hp : 19 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 19 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 19 (transLenTr ⟨77, by decide⟩ 19 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 19 (transLenTr ⟨77, by decide⟩ 19 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 19 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_19.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_20 (hp : 20 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 20 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 20 (transLenTr ⟨77, by decide⟩ 20 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 20 (transLenTr ⟨77, by decide⟩ 20 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 20 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_20.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_21 (hp : 21 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 21 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 21 (transLenTr ⟨77, by decide⟩ 21 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 21 (transLenTr ⟨77, by decide⟩ 21 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 21 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_21.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_22 (hp : 22 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 22 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 22 (transLenTr ⟨77, by decide⟩ 22 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 22 (transLenTr ⟨77, by decide⟩ 22 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 22 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_22.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_23 (hp : 23 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 23 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 23 (transLenTr ⟨77, by decide⟩ 23 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 23 (transLenTr ⟨77, by decide⟩ 23 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 23 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_23.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_77_77_24 (hp : 24 < (Q2.transData.getD 77 []).length)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ 24 hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ 24 (transLenTr ⟨77, by decide⟩ 24 hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨77, by decide⟩ : Fin 148) ⟨77, by decide⟩ _
      (validAt ⟨77, by decide⟩ (listedAt ⟨77, by decide⟩ hj))
      (colE1 ⟨77, by decide⟩ 24 (transLenTr ⟨77, by decide⟩ 24 hp)) T77_77
      hfix77_77 hinj77_77 hcardT77_77
      (fun i => conj_mem_of_fixedPoints _ _ (T77_77 i) (hfix77_77 i) _)
      ⟨77, by decide⟩ ⟨77, by decide⟩ _
      (Q2.validAt ⟨77, by decide⟩ (Q2.listedAt ⟨77, by decide⟩
        (alnCheck_rep ⟨77, by decide⟩ hj hq).1))
      (colE2 ⟨77, by decide⟩ 24 hp) Q2.T77_77_2 Q2.hfix77_77_2 Q2.hinj77_77_2
      Q2.hcardT77_77_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T77_77_2 i) (Q2.hfix77_77_2 i) _)
      colCert_77_77_24.hD ?_).symm
  rw [alnId_77 j hj]


theorem leaf_78_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T78_6
      hfix78_6 hinj78_6 hcardT78_6
      (fun i => conj_mem_of_fixedPoints _ _ (T78_6 i) (hfix78_6 i) _)
      ⟨78, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T78_6_2 Q2.hfix78_6_2 Q2.hinj78_6_2
      Q2.hcardT78_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_6_2 i) (Q2.hfix78_6_2 i) _)
      colCert_78_6_0.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T78_6
      hfix78_6 hinj78_6 hcardT78_6
      (fun i => conj_mem_of_fixedPoints _ _ (T78_6 i) (hfix78_6 i) _)
      ⟨78, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T78_6_2 Q2.hfix78_6_2 Q2.hinj78_6_2
      Q2.hcardT78_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_6_2 i) (Q2.hfix78_6_2 i) _)
      colCert_78_6_1.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T78_6
      hfix78_6 hinj78_6 hcardT78_6
      (fun i => conj_mem_of_fixedPoints _ _ (T78_6 i) (hfix78_6 i) _)
      ⟨78, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T78_6_2 Q2.hfix78_6_2 Q2.hinj78_6_2
      Q2.hcardT78_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_6_2 i) (Q2.hfix78_6_2 i) _)
      colCert_78_6_2.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T78_6
      hfix78_6 hinj78_6 hcardT78_6
      (fun i => conj_mem_of_fixedPoints _ _ (T78_6 i) (hfix78_6 i) _)
      ⟨78, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T78_6_2 Q2.hfix78_6_2 Q2.hinj78_6_2
      Q2.hcardT78_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_6_2 i) (Q2.hfix78_6_2 i) _)
      colCert_78_6_3.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T78_6
      hfix78_6 hinj78_6 hcardT78_6
      (fun i => conj_mem_of_fixedPoints _ _ (T78_6 i) (hfix78_6 i) _)
      ⟨78, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T78_6_2 Q2.hfix78_6_2 Q2.hinj78_6_2
      Q2.hcardT78_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_6_2 i) (Q2.hfix78_6_2 i) _)
      colCert_78_6_4.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T78_12
      hfix78_12 hinj78_12 hcardT78_12
      (fun i => conj_mem_of_fixedPoints _ _ (T78_12 i) (hfix78_12 i) _)
      ⟨78, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T78_12_2 Q2.hfix78_12_2 Q2.hinj78_12_2
      Q2.hcardT78_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_12_2 i) (Q2.hfix78_12_2 i) _)
      colCert_78_12_0.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T78_12
      hfix78_12 hinj78_12 hcardT78_12
      (fun i => conj_mem_of_fixedPoints _ _ (T78_12 i) (hfix78_12 i) _)
      ⟨78, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T78_12_2 Q2.hfix78_12_2 Q2.hinj78_12_2
      Q2.hcardT78_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_12_2 i) (Q2.hfix78_12_2 i) _)
      colCert_78_12_1.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T78_12
      hfix78_12 hinj78_12 hcardT78_12
      (fun i => conj_mem_of_fixedPoints _ _ (T78_12 i) (hfix78_12 i) _)
      ⟨78, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T78_12_2 Q2.hfix78_12_2 Q2.hinj78_12_2
      Q2.hcardT78_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_12_2 i) (Q2.hfix78_12_2 i) _)
      colCert_78_12_2.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T78_12
      hfix78_12 hinj78_12 hcardT78_12
      (fun i => conj_mem_of_fixedPoints _ _ (T78_12 i) (hfix78_12 i) _)
      ⟨78, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T78_12_2 Q2.hfix78_12_2 Q2.hinj78_12_2
      Q2.hcardT78_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_12_2 i) (Q2.hfix78_12_2 i) _)
      colCert_78_12_3.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T78_12
      hfix78_12 hinj78_12 hcardT78_12
      (fun i => conj_mem_of_fixedPoints _ _ (T78_12 i) (hfix78_12 i) _)
      ⟨78, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T78_12_2 Q2.hfix78_12_2 Q2.hinj78_12_2
      Q2.hcardT78_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_12_2 i) (Q2.hfix78_12_2 i) _)
      colCert_78_12_4.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T78_24
      hfix78_24 hinj78_24 hcardT78_24
      (fun i => conj_mem_of_fixedPoints _ _ (T78_24 i) (hfix78_24 i) _)
      ⟨78, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T78_24_2 Q2.hfix78_24_2 Q2.hinj78_24_2
      Q2.hcardT78_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_24_2 i) (Q2.hfix78_24_2 i) _)
      colCert_78_24_0.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T78_24
      hfix78_24 hinj78_24 hcardT78_24
      (fun i => conj_mem_of_fixedPoints _ _ (T78_24 i) (hfix78_24 i) _)
      ⟨78, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T78_24_2 Q2.hfix78_24_2 Q2.hinj78_24_2
      Q2.hcardT78_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_24_2 i) (Q2.hfix78_24_2 i) _)
      colCert_78_24_1.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T78_24
      hfix78_24 hinj78_24 hcardT78_24
      (fun i => conj_mem_of_fixedPoints _ _ (T78_24 i) (hfix78_24 i) _)
      ⟨78, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T78_24_2 Q2.hfix78_24_2 Q2.hinj78_24_2
      Q2.hcardT78_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_24_2 i) (Q2.hfix78_24_2 i) _)
      colCert_78_24_2.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T78_24
      hfix78_24 hinj78_24 hcardT78_24
      (fun i => conj_mem_of_fixedPoints _ _ (T78_24 i) (hfix78_24 i) _)
      ⟨78, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T78_24_2 Q2.hfix78_24_2 Q2.hinj78_24_2
      Q2.hcardT78_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_24_2 i) (Q2.hfix78_24_2 i) _)
      colCert_78_24_3.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T78_24
      hfix78_24 hinj78_24 hcardT78_24
      (fun i => conj_mem_of_fixedPoints _ _ (T78_24 i) (hfix78_24 i) _)
      ⟨78, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T78_24_2 Q2.hfix78_24_2 Q2.hinj78_24_2
      Q2.hcardT78_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_24_2 i) (Q2.hfix78_24_2 i) _)
      colCert_78_24_4.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T78_24
      hfix78_24 hinj78_24 hcardT78_24
      (fun i => conj_mem_of_fixedPoints _ _ (T78_24 i) (hfix78_24 i) _)
      ⟨78, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T78_24_2 Q2.hfix78_24_2 Q2.hinj78_24_2
      Q2.hcardT78_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_24_2 i) (Q2.hfix78_24_2 i) _)
      colCert_78_24_5.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T78_24
      hfix78_24 hinj78_24 hcardT78_24
      (fun i => conj_mem_of_fixedPoints _ _ (T78_24 i) (hfix78_24 i) _)
      ⟨78, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T78_24_2 Q2.hfix78_24_2 Q2.hinj78_24_2
      Q2.hcardT78_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_24_2 i) (Q2.hfix78_24_2 i) _)
      colCert_78_24_10.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T78_24
      hfix78_24 hinj78_24 hcardT78_24
      (fun i => conj_mem_of_fixedPoints _ _ (T78_24 i) (hfix78_24 i) _)
      ⟨78, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T78_24_2 Q2.hfix78_24_2 Q2.hinj78_24_2
      Q2.hcardT78_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_24_2 i) (Q2.hfix78_24_2 i) _)
      colCert_78_24_15.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T78_24
      hfix78_24 hinj78_24 hcardT78_24
      (fun i => conj_mem_of_fixedPoints _ _ (T78_24 i) (hfix78_24 i) _)
      ⟨78, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T78_24_2 Q2.hfix78_24_2 Q2.hinj78_24_2
      Q2.hcardT78_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_24_2 i) (Q2.hfix78_24_2 i) _)
      colCert_78_24_20.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T78_32
      hfix78_32 hinj78_32 hcardT78_32
      (fun i => conj_mem_of_fixedPoints _ _ (T78_32 i) (hfix78_32 i) _)
      ⟨78, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T78_32_2 Q2.hfix78_32_2 Q2.hinj78_32_2
      Q2.hcardT78_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_32_2 i) (Q2.hfix78_32_2 i) _)
      colCert_78_32_0.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T78_32
      hfix78_32 hinj78_32 hcardT78_32
      (fun i => conj_mem_of_fixedPoints _ _ (T78_32 i) (hfix78_32 i) _)
      ⟨78, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T78_32_2 Q2.hfix78_32_2 Q2.hinj78_32_2
      Q2.hcardT78_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_32_2 i) (Q2.hfix78_32_2 i) _)
      colCert_78_32_1.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T78_32
      hfix78_32 hinj78_32 hcardT78_32
      (fun i => conj_mem_of_fixedPoints _ _ (T78_32 i) (hfix78_32 i) _)
      ⟨78, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T78_32_2 Q2.hfix78_32_2 Q2.hinj78_32_2
      Q2.hcardT78_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_32_2 i) (Q2.hfix78_32_2 i) _)
      colCert_78_32_2.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T78_32
      hfix78_32 hinj78_32 hcardT78_32
      (fun i => conj_mem_of_fixedPoints _ _ (T78_32 i) (hfix78_32 i) _)
      ⟨78, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T78_32_2 Q2.hfix78_32_2 Q2.hinj78_32_2
      Q2.hcardT78_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_32_2 i) (Q2.hfix78_32_2 i) _)
      colCert_78_32_3.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T78_32
      hfix78_32 hinj78_32 hcardT78_32
      (fun i => conj_mem_of_fixedPoints _ _ (T78_32 i) (hfix78_32 i) _)
      ⟨78, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T78_32_2 Q2.hfix78_32_2 Q2.hinj78_32_2
      Q2.hcardT78_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_32_2 i) (Q2.hfix78_32_2 i) _)
      colCert_78_32_4.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T78_32
      hfix78_32 hinj78_32 hcardT78_32
      (fun i => conj_mem_of_fixedPoints _ _ (T78_32 i) (hfix78_32 i) _)
      ⟨78, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T78_32_2 Q2.hfix78_32_2 Q2.hinj78_32_2
      Q2.hcardT78_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_32_2 i) (Q2.hfix78_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T78_32 = colFn colCertDiv_78_32_5.D1 (m := 5) from colCertDiv_78_32_5.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 5 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T78_32_2 = colFn colCertDiv_78_32_5.D2 (m := 5) from colCertDiv_78_32_5.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_32_5_match


theorem leaf_78_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T78_32
      hfix78_32 hinj78_32 hcardT78_32
      (fun i => conj_mem_of_fixedPoints _ _ (T78_32 i) (hfix78_32 i) _)
      ⟨78, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T78_32_2 Q2.hfix78_32_2 Q2.hinj78_32_2
      Q2.hcardT78_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_32_2 i) (Q2.hfix78_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T78_32 = colFn colCertDiv_78_32_10.D1 (m := 5) from colCertDiv_78_32_10.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 10 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T78_32_2 = colFn colCertDiv_78_32_10.D2 (m := 5) from colCertDiv_78_32_10.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_32_10_match


theorem leaf_78_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T78_32
      hfix78_32 hinj78_32 hcardT78_32
      (fun i => conj_mem_of_fixedPoints _ _ (T78_32 i) (hfix78_32 i) _)
      ⟨78, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T78_32_2 Q2.hfix78_32_2 Q2.hinj78_32_2
      Q2.hcardT78_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_32_2 i) (Q2.hfix78_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T78_32 = colFn colCertDiv_78_32_15.D1 (m := 5) from colCertDiv_78_32_15.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 15 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T78_32_2 = colFn colCertDiv_78_32_15.D2 (m := 5) from colCertDiv_78_32_15.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_32_15_match


theorem leaf_78_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T78_32
      hfix78_32 hinj78_32 hcardT78_32
      (fun i => conj_mem_of_fixedPoints _ _ (T78_32 i) (hfix78_32 i) _)
      ⟨78, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T78_32_2 Q2.hfix78_32_2 Q2.hinj78_32_2
      Q2.hcardT78_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_32_2 i) (Q2.hfix78_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T78_32 = colFn colCertDiv_78_32_20.D1 (m := 5) from colCertDiv_78_32_20.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 20 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T78_32_2 = colFn colCertDiv_78_32_20.D2 (m := 5) from colCertDiv_78_32_20.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_32_20_match


theorem leaf_78_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T78_37
      hfix78_37 hinj78_37 hcardT78_37
      (fun i => conj_mem_of_fixedPoints _ _ (T78_37 i) (hfix78_37 i) _)
      ⟨78, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T78_37_2 Q2.hfix78_37_2 Q2.hinj78_37_2
      Q2.hcardT78_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_37_2 i) (Q2.hfix78_37_2 i) _)
      colCert_78_37_0.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T78_37
      hfix78_37 hinj78_37 hcardT78_37
      (fun i => conj_mem_of_fixedPoints _ _ (T78_37 i) (hfix78_37 i) _)
      ⟨78, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T78_37_2 Q2.hfix78_37_2 Q2.hinj78_37_2
      Q2.hcardT78_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_37_2 i) (Q2.hfix78_37_2 i) _)
      colCert_78_37_1.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T78_37
      hfix78_37 hinj78_37 hcardT78_37
      (fun i => conj_mem_of_fixedPoints _ _ (T78_37 i) (hfix78_37 i) _)
      ⟨78, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T78_37_2 Q2.hfix78_37_2 Q2.hinj78_37_2
      Q2.hcardT78_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_37_2 i) (Q2.hfix78_37_2 i) _)
      colCert_78_37_2.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T78_37
      hfix78_37 hinj78_37 hcardT78_37
      (fun i => conj_mem_of_fixedPoints _ _ (T78_37 i) (hfix78_37 i) _)
      ⟨78, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T78_37_2 Q2.hfix78_37_2 Q2.hinj78_37_2
      Q2.hcardT78_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_37_2 i) (Q2.hfix78_37_2 i) _)
      colCert_78_37_3.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T78_37
      hfix78_37 hinj78_37 hcardT78_37
      (fun i => conj_mem_of_fixedPoints _ _ (T78_37 i) (hfix78_37 i) _)
      ⟨78, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T78_37_2 Q2.hfix78_37_2 Q2.hinj78_37_2
      Q2.hcardT78_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_37_2 i) (Q2.hfix78_37_2 i) _)
      colCert_78_37_4.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T78_37
      hfix78_37 hinj78_37 hcardT78_37
      (fun i => conj_mem_of_fixedPoints _ _ (T78_37 i) (hfix78_37 i) _)
      ⟨78, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T78_37_2 Q2.hfix78_37_2 Q2.hinj78_37_2
      Q2.hcardT78_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_37_2 i) (Q2.hfix78_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T78_37 = colFn colCertDiv_78_37_5.D1 (m := 5) from colCertDiv_78_37_5.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T78_37_2 = colFn colCertDiv_78_37_5.D2 (m := 5) from colCertDiv_78_37_5.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_37_5_match


theorem leaf_78_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T78_37
      hfix78_37 hinj78_37 hcardT78_37
      (fun i => conj_mem_of_fixedPoints _ _ (T78_37 i) (hfix78_37 i) _)
      ⟨78, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T78_37_2 Q2.hfix78_37_2 Q2.hinj78_37_2
      Q2.hcardT78_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_37_2 i) (Q2.hfix78_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T78_37 = colFn colCertDiv_78_37_10.D1 (m := 5) from colCertDiv_78_37_10.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T78_37_2 = colFn colCertDiv_78_37_10.D2 (m := 5) from colCertDiv_78_37_10.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_37_10_match


theorem leaf_78_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T78_37
      hfix78_37 hinj78_37 hcardT78_37
      (fun i => conj_mem_of_fixedPoints _ _ (T78_37 i) (hfix78_37 i) _)
      ⟨78, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T78_37_2 Q2.hfix78_37_2 Q2.hinj78_37_2
      Q2.hcardT78_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_37_2 i) (Q2.hfix78_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T78_37 = colFn colCertDiv_78_37_15.D1 (m := 5) from colCertDiv_78_37_15.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T78_37_2 = colFn colCertDiv_78_37_15.D2 (m := 5) from colCertDiv_78_37_15.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_37_15_match


theorem leaf_78_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T78_37
      hfix78_37 hinj78_37 hcardT78_37
      (fun i => conj_mem_of_fixedPoints _ _ (T78_37 i) (hfix78_37 i) _)
      ⟨78, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T78_37_2 Q2.hfix78_37_2 Q2.hinj78_37_2
      Q2.hcardT78_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_37_2 i) (Q2.hfix78_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T78_37 = colFn colCertDiv_78_37_20.D1 (m := 5) from colCertDiv_78_37_20.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T78_37_2 = colFn colCertDiv_78_37_20.D2 (m := 5) from colCertDiv_78_37_20.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_37_20_match


theorem leaf_78_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T78_42
      hfix78_42 hinj78_42 hcardT78_42
      (fun i => conj_mem_of_fixedPoints _ _ (T78_42 i) (hfix78_42 i) _)
      ⟨78, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T78_42_2 Q2.hfix78_42_2 Q2.hinj78_42_2
      Q2.hcardT78_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_42_2 i) (Q2.hfix78_42_2 i) _)
      colCert_78_42_0.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T78_42
      hfix78_42 hinj78_42 hcardT78_42
      (fun i => conj_mem_of_fixedPoints _ _ (T78_42 i) (hfix78_42 i) _)
      ⟨78, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T78_42_2 Q2.hfix78_42_2 Q2.hinj78_42_2
      Q2.hcardT78_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_42_2 i) (Q2.hfix78_42_2 i) _)
      colCert_78_42_1.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T78_42
      hfix78_42 hinj78_42 hcardT78_42
      (fun i => conj_mem_of_fixedPoints _ _ (T78_42 i) (hfix78_42 i) _)
      ⟨78, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T78_42_2 Q2.hfix78_42_2 Q2.hinj78_42_2
      Q2.hcardT78_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_42_2 i) (Q2.hfix78_42_2 i) _)
      colCert_78_42_2.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T78_42
      hfix78_42 hinj78_42 hcardT78_42
      (fun i => conj_mem_of_fixedPoints _ _ (T78_42 i) (hfix78_42 i) _)
      ⟨78, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T78_42_2 Q2.hfix78_42_2 Q2.hinj78_42_2
      Q2.hcardT78_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_42_2 i) (Q2.hfix78_42_2 i) _)
      colCert_78_42_3.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T78_42
      hfix78_42 hinj78_42 hcardT78_42
      (fun i => conj_mem_of_fixedPoints _ _ (T78_42 i) (hfix78_42 i) _)
      ⟨78, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T78_42_2 Q2.hfix78_42_2 Q2.hinj78_42_2
      Q2.hcardT78_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_42_2 i) (Q2.hfix78_42_2 i) _)
      colCert_78_42_4.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T78_42
      hfix78_42 hinj78_42 hcardT78_42
      (fun i => conj_mem_of_fixedPoints _ _ (T78_42 i) (hfix78_42 i) _)
      ⟨78, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T78_42_2 Q2.hfix78_42_2 Q2.hinj78_42_2
      Q2.hcardT78_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_42_2 i) (Q2.hfix78_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T78_42 = colFn colCertDiv_78_42_5.D1 (m := 5) from colCertDiv_78_42_5.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T78_42_2 = colFn colCertDiv_78_42_5.D2 (m := 5) from colCertDiv_78_42_5.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_42_5_match


theorem leaf_78_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T78_42
      hfix78_42 hinj78_42 hcardT78_42
      (fun i => conj_mem_of_fixedPoints _ _ (T78_42 i) (hfix78_42 i) _)
      ⟨78, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T78_42_2 Q2.hfix78_42_2 Q2.hinj78_42_2
      Q2.hcardT78_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_42_2 i) (Q2.hfix78_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T78_42 = colFn colCertDiv_78_42_10.D1 (m := 5) from colCertDiv_78_42_10.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T78_42_2 = colFn colCertDiv_78_42_10.D2 (m := 5) from colCertDiv_78_42_10.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_42_10_match


theorem leaf_78_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T78_42
      hfix78_42 hinj78_42 hcardT78_42
      (fun i => conj_mem_of_fixedPoints _ _ (T78_42 i) (hfix78_42 i) _)
      ⟨78, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T78_42_2 Q2.hfix78_42_2 Q2.hinj78_42_2
      Q2.hcardT78_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_42_2 i) (Q2.hfix78_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T78_42 = colFn colCertDiv_78_42_15.D1 (m := 5) from colCertDiv_78_42_15.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T78_42_2 = colFn colCertDiv_78_42_15.D2 (m := 5) from colCertDiv_78_42_15.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_42_15_match


theorem leaf_78_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T78_42
      hfix78_42 hinj78_42 hcardT78_42
      (fun i => conj_mem_of_fixedPoints _ _ (T78_42 i) (hfix78_42 i) _)
      ⟨78, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T78_42_2 Q2.hfix78_42_2 Q2.hinj78_42_2
      Q2.hcardT78_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_42_2 i) (Q2.hfix78_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T78_42 = colFn colCertDiv_78_42_20.D1 (m := 5) from colCertDiv_78_42_20.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T78_42_2 = colFn colCertDiv_78_42_20.D2 (m := 5) from colCertDiv_78_42_20.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_42_20_match


theorem leaf_78_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T78_47
      hfix78_47 hinj78_47 hcardT78_47
      (fun i => conj_mem_of_fixedPoints _ _ (T78_47 i) (hfix78_47 i) _)
      ⟨78, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T78_47_2 Q2.hfix78_47_2 Q2.hinj78_47_2
      Q2.hcardT78_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_47_2 i) (Q2.hfix78_47_2 i) _)
      colCert_78_47_0.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T78_47
      hfix78_47 hinj78_47 hcardT78_47
      (fun i => conj_mem_of_fixedPoints _ _ (T78_47 i) (hfix78_47 i) _)
      ⟨78, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T78_47_2 Q2.hfix78_47_2 Q2.hinj78_47_2
      Q2.hcardT78_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_47_2 i) (Q2.hfix78_47_2 i) _)
      colCert_78_47_1.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T78_47
      hfix78_47 hinj78_47 hcardT78_47
      (fun i => conj_mem_of_fixedPoints _ _ (T78_47 i) (hfix78_47 i) _)
      ⟨78, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T78_47_2 Q2.hfix78_47_2 Q2.hinj78_47_2
      Q2.hcardT78_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_47_2 i) (Q2.hfix78_47_2 i) _)
      colCert_78_47_2.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T78_47
      hfix78_47 hinj78_47 hcardT78_47
      (fun i => conj_mem_of_fixedPoints _ _ (T78_47 i) (hfix78_47 i) _)
      ⟨78, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T78_47_2 Q2.hfix78_47_2 Q2.hinj78_47_2
      Q2.hcardT78_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_47_2 i) (Q2.hfix78_47_2 i) _)
      colCert_78_47_3.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T78_47
      hfix78_47 hinj78_47 hcardT78_47
      (fun i => conj_mem_of_fixedPoints _ _ (T78_47 i) (hfix78_47 i) _)
      ⟨78, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T78_47_2 Q2.hfix78_47_2 Q2.hinj78_47_2
      Q2.hcardT78_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_47_2 i) (Q2.hfix78_47_2 i) _)
      colCert_78_47_4.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T78_47
      hfix78_47 hinj78_47 hcardT78_47
      (fun i => conj_mem_of_fixedPoints _ _ (T78_47 i) (hfix78_47 i) _)
      ⟨78, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T78_47_2 Q2.hfix78_47_2 Q2.hinj78_47_2
      Q2.hcardT78_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_47_2 i) (Q2.hfix78_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T78_47 = colFn colCertDiv_78_47_5.D1 (m := 5) from colCertDiv_78_47_5.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T78_47_2 = colFn colCertDiv_78_47_5.D2 (m := 5) from colCertDiv_78_47_5.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_47_5_match


theorem leaf_78_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T78_47
      hfix78_47 hinj78_47 hcardT78_47
      (fun i => conj_mem_of_fixedPoints _ _ (T78_47 i) (hfix78_47 i) _)
      ⟨78, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T78_47_2 Q2.hfix78_47_2 Q2.hinj78_47_2
      Q2.hcardT78_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_47_2 i) (Q2.hfix78_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T78_47 = colFn colCertDiv_78_47_10.D1 (m := 5) from colCertDiv_78_47_10.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T78_47_2 = colFn colCertDiv_78_47_10.D2 (m := 5) from colCertDiv_78_47_10.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_47_10_match


theorem leaf_78_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T78_47
      hfix78_47 hinj78_47 hcardT78_47
      (fun i => conj_mem_of_fixedPoints _ _ (T78_47 i) (hfix78_47 i) _)
      ⟨78, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T78_47_2 Q2.hfix78_47_2 Q2.hinj78_47_2
      Q2.hcardT78_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_47_2 i) (Q2.hfix78_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T78_47 = colFn colCertDiv_78_47_15.D1 (m := 5) from colCertDiv_78_47_15.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T78_47_2 = colFn colCertDiv_78_47_15.D2 (m := 5) from colCertDiv_78_47_15.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_47_15_match


theorem leaf_78_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T78_47
      hfix78_47 hinj78_47 hcardT78_47
      (fun i => conj_mem_of_fixedPoints _ _ (T78_47 i) (hfix78_47 i) _)
      ⟨78, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T78_47_2 Q2.hfix78_47_2 Q2.hinj78_47_2
      Q2.hcardT78_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_47_2 i) (Q2.hfix78_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T78_47 = colFn colCertDiv_78_47_20.D1 (m := 5) from colCertDiv_78_47_20.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T78_47_2 = colFn colCertDiv_78_47_20.D2 (m := 5) from colCertDiv_78_47_20.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_47_20_match


theorem leaf_78_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T78_52
      hfix78_52 hinj78_52 hcardT78_52
      (fun i => conj_mem_of_fixedPoints _ _ (T78_52 i) (hfix78_52 i) _)
      ⟨78, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T78_52_2 Q2.hfix78_52_2 Q2.hinj78_52_2
      Q2.hcardT78_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_52_2 i) (Q2.hfix78_52_2 i) _)
      colCert_78_52_0.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T78_52
      hfix78_52 hinj78_52 hcardT78_52
      (fun i => conj_mem_of_fixedPoints _ _ (T78_52 i) (hfix78_52 i) _)
      ⟨78, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T78_52_2 Q2.hfix78_52_2 Q2.hinj78_52_2
      Q2.hcardT78_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_52_2 i) (Q2.hfix78_52_2 i) _)
      colCert_78_52_1.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T78_52
      hfix78_52 hinj78_52 hcardT78_52
      (fun i => conj_mem_of_fixedPoints _ _ (T78_52 i) (hfix78_52 i) _)
      ⟨78, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T78_52_2 Q2.hfix78_52_2 Q2.hinj78_52_2
      Q2.hcardT78_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_52_2 i) (Q2.hfix78_52_2 i) _)
      colCert_78_52_2.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T78_52
      hfix78_52 hinj78_52 hcardT78_52
      (fun i => conj_mem_of_fixedPoints _ _ (T78_52 i) (hfix78_52 i) _)
      ⟨78, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T78_52_2 Q2.hfix78_52_2 Q2.hinj78_52_2
      Q2.hcardT78_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_52_2 i) (Q2.hfix78_52_2 i) _)
      colCert_78_52_3.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T78_52
      hfix78_52 hinj78_52 hcardT78_52
      (fun i => conj_mem_of_fixedPoints _ _ (T78_52 i) (hfix78_52 i) _)
      ⟨78, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T78_52_2 Q2.hfix78_52_2 Q2.hinj78_52_2
      Q2.hcardT78_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_52_2 i) (Q2.hfix78_52_2 i) _)
      colCert_78_52_4.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T78_52
      hfix78_52 hinj78_52 hcardT78_52
      (fun i => conj_mem_of_fixedPoints _ _ (T78_52 i) (hfix78_52 i) _)
      ⟨78, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T78_52_2 Q2.hfix78_52_2 Q2.hinj78_52_2
      Q2.hcardT78_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_52_2 i) (Q2.hfix78_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T78_52 = colFn colCertDiv_78_52_5.D1 (m := 5) from colCertDiv_78_52_5.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T78_52_2 = colFn colCertDiv_78_52_5.D2 (m := 5) from colCertDiv_78_52_5.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_52_5_match


theorem leaf_78_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T78_52
      hfix78_52 hinj78_52 hcardT78_52
      (fun i => conj_mem_of_fixedPoints _ _ (T78_52 i) (hfix78_52 i) _)
      ⟨78, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T78_52_2 Q2.hfix78_52_2 Q2.hinj78_52_2
      Q2.hcardT78_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_52_2 i) (Q2.hfix78_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T78_52 = colFn colCertDiv_78_52_10.D1 (m := 5) from colCertDiv_78_52_10.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T78_52_2 = colFn colCertDiv_78_52_10.D2 (m := 5) from colCertDiv_78_52_10.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_52_10_match


theorem leaf_78_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T78_52
      hfix78_52 hinj78_52 hcardT78_52
      (fun i => conj_mem_of_fixedPoints _ _ (T78_52 i) (hfix78_52 i) _)
      ⟨78, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T78_52_2 Q2.hfix78_52_2 Q2.hinj78_52_2
      Q2.hcardT78_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_52_2 i) (Q2.hfix78_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T78_52 = colFn colCertDiv_78_52_15.D1 (m := 5) from colCertDiv_78_52_15.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T78_52_2 = colFn colCertDiv_78_52_15.D2 (m := 5) from colCertDiv_78_52_15.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_52_15_match


theorem leaf_78_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨78, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T78_52
      hfix78_52 hinj78_52 hcardT78_52
      (fun i => conj_mem_of_fixedPoints _ _ (T78_52 i) (hfix78_52 i) _)
      ⟨78, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T78_52_2 Q2.hfix78_52_2 Q2.hinj78_52_2
      Q2.hcardT78_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_52_2 i) (Q2.hfix78_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨78, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T78_52 = colFn colCertDiv_78_52_20.D1 (m := 5) from colCertDiv_78_52_20.bind1,
    show colData2 (⟨78, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T78_52_2 = colFn colCertDiv_78_52_20.D2 (m := 5) from colCertDiv_78_52_20.bind2]
  rw [alnId_78 j hj]
  exact fastcode_of_div ⟨78, by decide⟩ _ _ _
    ((alnId_78 j hj) ▸ Q2.listedAt (⟨78, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨78, by decide⟩ : Fin 148) hj hq).1) colCertDiv_78_52_20_match


theorem leaf_78_78_0 (hp : 0 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 0 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 0 (transLenTr ⟨78, by decide⟩ 0 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 0 (transLenTr ⟨78, by decide⟩ 0 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 0 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_0.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_1 (hp : 1 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 1 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 1 (transLenTr ⟨78, by decide⟩ 1 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 1 (transLenTr ⟨78, by decide⟩ 1 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 1 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_1.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_2 (hp : 2 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 2 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 2 (transLenTr ⟨78, by decide⟩ 2 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 2 (transLenTr ⟨78, by decide⟩ 2 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 2 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_2.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_3 (hp : 3 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 3 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 3 (transLenTr ⟨78, by decide⟩ 3 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 3 (transLenTr ⟨78, by decide⟩ 3 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 3 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_3.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_4 (hp : 4 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 4 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 4 (transLenTr ⟨78, by decide⟩ 4 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 4 (transLenTr ⟨78, by decide⟩ 4 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 4 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_4.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_5 (hp : 5 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 5 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 5 (transLenTr ⟨78, by decide⟩ 5 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 5 (transLenTr ⟨78, by decide⟩ 5 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 5 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_5.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_6 (hp : 6 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 6 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 6 (transLenTr ⟨78, by decide⟩ 6 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 6 (transLenTr ⟨78, by decide⟩ 6 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 6 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_6.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_7 (hp : 7 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 7 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 7 (transLenTr ⟨78, by decide⟩ 7 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 7 (transLenTr ⟨78, by decide⟩ 7 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 7 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_7.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_8 (hp : 8 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 8 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 8 (transLenTr ⟨78, by decide⟩ 8 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 8 (transLenTr ⟨78, by decide⟩ 8 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 8 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_8.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_9 (hp : 9 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 9 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 9 (transLenTr ⟨78, by decide⟩ 9 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 9 (transLenTr ⟨78, by decide⟩ 9 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 9 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_9.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_10 (hp : 10 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 10 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 10 (transLenTr ⟨78, by decide⟩ 10 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 10 (transLenTr ⟨78, by decide⟩ 10 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 10 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_10.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_11 (hp : 11 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 11 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 11 (transLenTr ⟨78, by decide⟩ 11 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 11 (transLenTr ⟨78, by decide⟩ 11 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 11 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_11.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_12 (hp : 12 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 12 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 12 (transLenTr ⟨78, by decide⟩ 12 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 12 (transLenTr ⟨78, by decide⟩ 12 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 12 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_12.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_13 (hp : 13 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 13 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 13 (transLenTr ⟨78, by decide⟩ 13 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 13 (transLenTr ⟨78, by decide⟩ 13 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 13 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_13.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_14 (hp : 14 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 14 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 14 (transLenTr ⟨78, by decide⟩ 14 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 14 (transLenTr ⟨78, by decide⟩ 14 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 14 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_14.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_15 (hp : 15 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 15 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 15 (transLenTr ⟨78, by decide⟩ 15 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 15 (transLenTr ⟨78, by decide⟩ 15 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 15 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_15.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_16 (hp : 16 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 16 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 16 (transLenTr ⟨78, by decide⟩ 16 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 16 (transLenTr ⟨78, by decide⟩ 16 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 16 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_16.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_17 (hp : 17 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 17 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 17 (transLenTr ⟨78, by decide⟩ 17 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 17 (transLenTr ⟨78, by decide⟩ 17 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 17 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_17.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_18 (hp : 18 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 18 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 18 (transLenTr ⟨78, by decide⟩ 18 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 18 (transLenTr ⟨78, by decide⟩ 18 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 18 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_18.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_19 (hp : 19 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 19 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 19 (transLenTr ⟨78, by decide⟩ 19 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 19 (transLenTr ⟨78, by decide⟩ 19 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 19 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_19.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_20 (hp : 20 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 20 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 20 (transLenTr ⟨78, by decide⟩ 20 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 20 (transLenTr ⟨78, by decide⟩ 20 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 20 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_20.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_21 (hp : 21 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 21 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 21 (transLenTr ⟨78, by decide⟩ 21 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 21 (transLenTr ⟨78, by decide⟩ 21 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 21 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_21.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_22 (hp : 22 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 22 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 22 (transLenTr ⟨78, by decide⟩ 22 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 22 (transLenTr ⟨78, by decide⟩ 22 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 22 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_22.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_23 (hp : 23 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 23 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 23 (transLenTr ⟨78, by decide⟩ 23 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 23 (transLenTr ⟨78, by decide⟩ 23 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 23 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_23.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_78_78_24 (hp : 24 < (Q2.transData.getD 78 []).length)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ 24 hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ 24 (transLenTr ⟨78, by decide⟩ 24 hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨78, by decide⟩ : Fin 148) ⟨78, by decide⟩ _
      (validAt ⟨78, by decide⟩ (listedAt ⟨78, by decide⟩ hj))
      (colE1 ⟨78, by decide⟩ 24 (transLenTr ⟨78, by decide⟩ 24 hp)) T78_78
      hfix78_78 hinj78_78 hcardT78_78
      (fun i => conj_mem_of_fixedPoints _ _ (T78_78 i) (hfix78_78 i) _)
      ⟨78, by decide⟩ ⟨78, by decide⟩ _
      (Q2.validAt ⟨78, by decide⟩ (Q2.listedAt ⟨78, by decide⟩
        (alnCheck_rep ⟨78, by decide⟩ hj hq).1))
      (colE2 ⟨78, by decide⟩ 24 hp) Q2.T78_78_2 Q2.hfix78_78_2 Q2.hinj78_78_2
      Q2.hcardT78_78_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T78_78_2 i) (Q2.hfix78_78_2 i) _)
      colCert_78_78_24.hD ?_).symm
  rw [alnId_78 j hj]


theorem leaf_79_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T79_8
      hfix79_8 hinj79_8 hcardT79_8
      (fun i => conj_mem_of_fixedPoints _ _ (T79_8 i) (hfix79_8 i) _)
      ⟨79, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T79_8_2 Q2.hfix79_8_2 Q2.hinj79_8_2
      Q2.hcardT79_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_8_2 i) (Q2.hfix79_8_2 i) _)
      colCert_79_8_0.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T79_8
      hfix79_8 hinj79_8 hcardT79_8
      (fun i => conj_mem_of_fixedPoints _ _ (T79_8 i) (hfix79_8 i) _)
      ⟨79, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T79_8_2 Q2.hfix79_8_2 Q2.hinj79_8_2
      Q2.hcardT79_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_8_2 i) (Q2.hfix79_8_2 i) _)
      colCert_79_8_1.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T79_8
      hfix79_8 hinj79_8 hcardT79_8
      (fun i => conj_mem_of_fixedPoints _ _ (T79_8 i) (hfix79_8 i) _)
      ⟨79, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T79_8_2 Q2.hfix79_8_2 Q2.hinj79_8_2
      Q2.hcardT79_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_8_2 i) (Q2.hfix79_8_2 i) _)
      colCert_79_8_2.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T79_8
      hfix79_8 hinj79_8 hcardT79_8
      (fun i => conj_mem_of_fixedPoints _ _ (T79_8 i) (hfix79_8 i) _)
      ⟨79, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T79_8_2 Q2.hfix79_8_2 Q2.hinj79_8_2
      Q2.hcardT79_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_8_2 i) (Q2.hfix79_8_2 i) _)
      colCert_79_8_3.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T79_8
      hfix79_8 hinj79_8 hcardT79_8
      (fun i => conj_mem_of_fixedPoints _ _ (T79_8 i) (hfix79_8 i) _)
      ⟨79, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T79_8_2 Q2.hfix79_8_2 Q2.hinj79_8_2
      Q2.hcardT79_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_8_2 i) (Q2.hfix79_8_2 i) _)
      colCert_79_8_4.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T79_12
      hfix79_12 hinj79_12 hcardT79_12
      (fun i => conj_mem_of_fixedPoints _ _ (T79_12 i) (hfix79_12 i) _)
      ⟨79, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T79_12_2 Q2.hfix79_12_2 Q2.hinj79_12_2
      Q2.hcardT79_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_12_2 i) (Q2.hfix79_12_2 i) _)
      colCert_79_12_0.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T79_12
      hfix79_12 hinj79_12 hcardT79_12
      (fun i => conj_mem_of_fixedPoints _ _ (T79_12 i) (hfix79_12 i) _)
      ⟨79, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T79_12_2 Q2.hfix79_12_2 Q2.hinj79_12_2
      Q2.hcardT79_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_12_2 i) (Q2.hfix79_12_2 i) _)
      colCert_79_12_1.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T79_12
      hfix79_12 hinj79_12 hcardT79_12
      (fun i => conj_mem_of_fixedPoints _ _ (T79_12 i) (hfix79_12 i) _)
      ⟨79, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T79_12_2 Q2.hfix79_12_2 Q2.hinj79_12_2
      Q2.hcardT79_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_12_2 i) (Q2.hfix79_12_2 i) _)
      colCert_79_12_2.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T79_12
      hfix79_12 hinj79_12 hcardT79_12
      (fun i => conj_mem_of_fixedPoints _ _ (T79_12 i) (hfix79_12 i) _)
      ⟨79, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T79_12_2 Q2.hfix79_12_2 Q2.hinj79_12_2
      Q2.hcardT79_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_12_2 i) (Q2.hfix79_12_2 i) _)
      colCert_79_12_3.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T79_12
      hfix79_12 hinj79_12 hcardT79_12
      (fun i => conj_mem_of_fixedPoints _ _ (T79_12 i) (hfix79_12 i) _)
      ⟨79, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T79_12_2 Q2.hfix79_12_2 Q2.hinj79_12_2
      Q2.hcardT79_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_12_2 i) (Q2.hfix79_12_2 i) _)
      colCert_79_12_4.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T79_26
      hfix79_26 hinj79_26 hcardT79_26
      (fun i => conj_mem_of_fixedPoints _ _ (T79_26 i) (hfix79_26 i) _)
      ⟨79, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T79_26_2 Q2.hfix79_26_2 Q2.hinj79_26_2
      Q2.hcardT79_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_26_2 i) (Q2.hfix79_26_2 i) _)
      colCert_79_26_0.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T79_26
      hfix79_26 hinj79_26 hcardT79_26
      (fun i => conj_mem_of_fixedPoints _ _ (T79_26 i) (hfix79_26 i) _)
      ⟨79, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T79_26_2 Q2.hfix79_26_2 Q2.hinj79_26_2
      Q2.hcardT79_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_26_2 i) (Q2.hfix79_26_2 i) _)
      colCert_79_26_1.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T79_26
      hfix79_26 hinj79_26 hcardT79_26
      (fun i => conj_mem_of_fixedPoints _ _ (T79_26 i) (hfix79_26 i) _)
      ⟨79, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T79_26_2 Q2.hfix79_26_2 Q2.hinj79_26_2
      Q2.hcardT79_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_26_2 i) (Q2.hfix79_26_2 i) _)
      colCert_79_26_2.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T79_26
      hfix79_26 hinj79_26 hcardT79_26
      (fun i => conj_mem_of_fixedPoints _ _ (T79_26 i) (hfix79_26 i) _)
      ⟨79, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T79_26_2 Q2.hfix79_26_2 Q2.hinj79_26_2
      Q2.hcardT79_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_26_2 i) (Q2.hfix79_26_2 i) _)
      colCert_79_26_3.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T79_26
      hfix79_26 hinj79_26 hcardT79_26
      (fun i => conj_mem_of_fixedPoints _ _ (T79_26 i) (hfix79_26 i) _)
      ⟨79, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T79_26_2 Q2.hfix79_26_2 Q2.hinj79_26_2
      Q2.hcardT79_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_26_2 i) (Q2.hfix79_26_2 i) _)
      colCert_79_26_4.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T79_26
      hfix79_26 hinj79_26 hcardT79_26
      (fun i => conj_mem_of_fixedPoints _ _ (T79_26 i) (hfix79_26 i) _)
      ⟨79, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T79_26_2 Q2.hfix79_26_2 Q2.hinj79_26_2
      Q2.hcardT79_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_26_2 i) (Q2.hfix79_26_2 i) _)
      colCert_79_26_5.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T79_26
      hfix79_26 hinj79_26 hcardT79_26
      (fun i => conj_mem_of_fixedPoints _ _ (T79_26 i) (hfix79_26 i) _)
      ⟨79, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T79_26_2 Q2.hfix79_26_2 Q2.hinj79_26_2
      Q2.hcardT79_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_26_2 i) (Q2.hfix79_26_2 i) _)
      colCert_79_26_10.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T79_26
      hfix79_26 hinj79_26 hcardT79_26
      (fun i => conj_mem_of_fixedPoints _ _ (T79_26 i) (hfix79_26 i) _)
      ⟨79, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T79_26_2 Q2.hfix79_26_2 Q2.hinj79_26_2
      Q2.hcardT79_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_26_2 i) (Q2.hfix79_26_2 i) _)
      colCert_79_26_15.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T79_26
      hfix79_26 hinj79_26 hcardT79_26
      (fun i => conj_mem_of_fixedPoints _ _ (T79_26 i) (hfix79_26 i) _)
      ⟨79, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T79_26_2 Q2.hfix79_26_2 Q2.hinj79_26_2
      Q2.hcardT79_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_26_2 i) (Q2.hfix79_26_2 i) _)
      colCert_79_26_20.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_32_0 (hp : 0 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 0 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 0 (transLenTr ⟨32, by decide⟩ 0 hp)) T79_32
      hfix79_32 hinj79_32 hcardT79_32
      (fun i => conj_mem_of_fixedPoints _ _ (T79_32 i) (hfix79_32 i) _)
      ⟨79, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 0 hp) Q2.T79_32_2 Q2.hfix79_32_2 Q2.hinj79_32_2
      Q2.hcardT79_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_32_2 i) (Q2.hfix79_32_2 i) _)
      colCert_79_32_0.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_32_1 (hp : 1 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 1 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 1 (transLenTr ⟨32, by decide⟩ 1 hp)) T79_32
      hfix79_32 hinj79_32 hcardT79_32
      (fun i => conj_mem_of_fixedPoints _ _ (T79_32 i) (hfix79_32 i) _)
      ⟨79, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 1 hp) Q2.T79_32_2 Q2.hfix79_32_2 Q2.hinj79_32_2
      Q2.hcardT79_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_32_2 i) (Q2.hfix79_32_2 i) _)
      colCert_79_32_1.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_32_2 (hp : 2 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 2 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 2 (transLenTr ⟨32, by decide⟩ 2 hp)) T79_32
      hfix79_32 hinj79_32 hcardT79_32
      (fun i => conj_mem_of_fixedPoints _ _ (T79_32 i) (hfix79_32 i) _)
      ⟨79, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 2 hp) Q2.T79_32_2 Q2.hfix79_32_2 Q2.hinj79_32_2
      Q2.hcardT79_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_32_2 i) (Q2.hfix79_32_2 i) _)
      colCert_79_32_2.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_32_3 (hp : 3 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 3 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 3 (transLenTr ⟨32, by decide⟩ 3 hp)) T79_32
      hfix79_32 hinj79_32 hcardT79_32
      (fun i => conj_mem_of_fixedPoints _ _ (T79_32 i) (hfix79_32 i) _)
      ⟨79, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 3 hp) Q2.T79_32_2 Q2.hfix79_32_2 Q2.hinj79_32_2
      Q2.hcardT79_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_32_2 i) (Q2.hfix79_32_2 i) _)
      colCert_79_32_3.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_32_4 (hp : 4 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 4 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 4 (transLenTr ⟨32, by decide⟩ 4 hp)) T79_32
      hfix79_32 hinj79_32 hcardT79_32
      (fun i => conj_mem_of_fixedPoints _ _ (T79_32 i) (hfix79_32 i) _)
      ⟨79, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 4 hp) Q2.T79_32_2 Q2.hfix79_32_2 Q2.hinj79_32_2
      Q2.hcardT79_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_32_2 i) (Q2.hfix79_32_2 i) _)
      colCert_79_32_4.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_32_5 (hp : 5 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 5 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp)) T79_32
      hfix79_32 hinj79_32 hcardT79_32
      (fun i => conj_mem_of_fixedPoints _ _ (T79_32 i) (hfix79_32 i) _)
      ⟨79, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 5 hp) Q2.T79_32_2 Q2.hfix79_32_2 Q2.hinj79_32_2
      Q2.hcardT79_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_32_2 i) (Q2.hfix79_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 5 (transLenTr ⟨32, by decide⟩ 5 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T79_32 = colFn colCertDiv_79_32_5.D1 (m := 5) from colCertDiv_79_32_5.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 5 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T79_32_2 = colFn colCertDiv_79_32_5.D2 (m := 5) from colCertDiv_79_32_5.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_32_5_match


theorem leaf_79_32_10 (hp : 10 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 10 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp)) T79_32
      hfix79_32 hinj79_32 hcardT79_32
      (fun i => conj_mem_of_fixedPoints _ _ (T79_32 i) (hfix79_32 i) _)
      ⟨79, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 10 hp) Q2.T79_32_2 Q2.hfix79_32_2 Q2.hinj79_32_2
      Q2.hcardT79_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_32_2 i) (Q2.hfix79_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 10 (transLenTr ⟨32, by decide⟩ 10 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T79_32 = colFn colCertDiv_79_32_10.D1 (m := 5) from colCertDiv_79_32_10.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 10 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T79_32_2 = colFn colCertDiv_79_32_10.D2 (m := 5) from colCertDiv_79_32_10.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_32_10_match


theorem leaf_79_32_15 (hp : 15 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 15 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp)) T79_32
      hfix79_32 hinj79_32 hcardT79_32
      (fun i => conj_mem_of_fixedPoints _ _ (T79_32 i) (hfix79_32 i) _)
      ⟨79, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 15 hp) Q2.T79_32_2 Q2.hfix79_32_2 Q2.hinj79_32_2
      Q2.hcardT79_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_32_2 i) (Q2.hfix79_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 15 (transLenTr ⟨32, by decide⟩ 15 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T79_32 = colFn colCertDiv_79_32_15.D1 (m := 5) from colCertDiv_79_32_15.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 15 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T79_32_2 = colFn colCertDiv_79_32_15.D2 (m := 5) from colCertDiv_79_32_15.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_32_15_match


theorem leaf_79_32_20 (hp : 20 < (Q2.transData.getD 32 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ 20 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨32, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp)) T79_32
      hfix79_32 hinj79_32 hcardT79_32
      (fun i => conj_mem_of_fixedPoints _ _ (T79_32 i) (hfix79_32 i) _)
      ⟨79, by decide⟩ ⟨32, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨32, by decide⟩ 20 hp) Q2.T79_32_2 Q2.hfix79_32_2 Q2.hinj79_32_2
      Q2.hcardT79_32_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_32_2 i) (Q2.hfix79_32_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨32, by decide⟩ 20 (transLenTr ⟨32, by decide⟩ 20 hp) : ↥(reps ⟨32, by decide⟩)) : Coordinate 1)
        T79_32 = colFn colCertDiv_79_32_20.D1 (m := 5) from colCertDiv_79_32_20.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨32, by decide⟩ 20 hp : ↥(Q2.reps ⟨32, by decide⟩)) : Coordinate 2)
        Q2.T79_32_2 = colFn colCertDiv_79_32_20.D2 (m := 5) from colCertDiv_79_32_20.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_32_20_match


theorem leaf_79_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T79_37
      hfix79_37 hinj79_37 hcardT79_37
      (fun i => conj_mem_of_fixedPoints _ _ (T79_37 i) (hfix79_37 i) _)
      ⟨79, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T79_37_2 Q2.hfix79_37_2 Q2.hinj79_37_2
      Q2.hcardT79_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_37_2 i) (Q2.hfix79_37_2 i) _)
      colCert_79_37_0.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T79_37
      hfix79_37 hinj79_37 hcardT79_37
      (fun i => conj_mem_of_fixedPoints _ _ (T79_37 i) (hfix79_37 i) _)
      ⟨79, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T79_37_2 Q2.hfix79_37_2 Q2.hinj79_37_2
      Q2.hcardT79_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_37_2 i) (Q2.hfix79_37_2 i) _)
      colCert_79_37_1.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T79_37
      hfix79_37 hinj79_37 hcardT79_37
      (fun i => conj_mem_of_fixedPoints _ _ (T79_37 i) (hfix79_37 i) _)
      ⟨79, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T79_37_2 Q2.hfix79_37_2 Q2.hinj79_37_2
      Q2.hcardT79_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_37_2 i) (Q2.hfix79_37_2 i) _)
      colCert_79_37_2.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T79_37
      hfix79_37 hinj79_37 hcardT79_37
      (fun i => conj_mem_of_fixedPoints _ _ (T79_37 i) (hfix79_37 i) _)
      ⟨79, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T79_37_2 Q2.hfix79_37_2 Q2.hinj79_37_2
      Q2.hcardT79_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_37_2 i) (Q2.hfix79_37_2 i) _)
      colCert_79_37_3.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T79_37
      hfix79_37 hinj79_37 hcardT79_37
      (fun i => conj_mem_of_fixedPoints _ _ (T79_37 i) (hfix79_37 i) _)
      ⟨79, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T79_37_2 Q2.hfix79_37_2 Q2.hinj79_37_2
      Q2.hcardT79_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_37_2 i) (Q2.hfix79_37_2 i) _)
      colCert_79_37_4.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T79_37
      hfix79_37 hinj79_37 hcardT79_37
      (fun i => conj_mem_of_fixedPoints _ _ (T79_37 i) (hfix79_37 i) _)
      ⟨79, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T79_37_2 Q2.hfix79_37_2 Q2.hinj79_37_2
      Q2.hcardT79_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_37_2 i) (Q2.hfix79_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T79_37 = colFn colCertDiv_79_37_5.D1 (m := 5) from colCertDiv_79_37_5.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T79_37_2 = colFn colCertDiv_79_37_5.D2 (m := 5) from colCertDiv_79_37_5.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_37_5_match


theorem leaf_79_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T79_37
      hfix79_37 hinj79_37 hcardT79_37
      (fun i => conj_mem_of_fixedPoints _ _ (T79_37 i) (hfix79_37 i) _)
      ⟨79, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T79_37_2 Q2.hfix79_37_2 Q2.hinj79_37_2
      Q2.hcardT79_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_37_2 i) (Q2.hfix79_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T79_37 = colFn colCertDiv_79_37_10.D1 (m := 5) from colCertDiv_79_37_10.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T79_37_2 = colFn colCertDiv_79_37_10.D2 (m := 5) from colCertDiv_79_37_10.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_37_10_match


theorem leaf_79_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T79_37
      hfix79_37 hinj79_37 hcardT79_37
      (fun i => conj_mem_of_fixedPoints _ _ (T79_37 i) (hfix79_37 i) _)
      ⟨79, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T79_37_2 Q2.hfix79_37_2 Q2.hinj79_37_2
      Q2.hcardT79_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_37_2 i) (Q2.hfix79_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T79_37 = colFn colCertDiv_79_37_15.D1 (m := 5) from colCertDiv_79_37_15.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T79_37_2 = colFn colCertDiv_79_37_15.D2 (m := 5) from colCertDiv_79_37_15.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_37_15_match


theorem leaf_79_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T79_37
      hfix79_37 hinj79_37 hcardT79_37
      (fun i => conj_mem_of_fixedPoints _ _ (T79_37 i) (hfix79_37 i) _)
      ⟨79, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T79_37_2 Q2.hfix79_37_2 Q2.hinj79_37_2
      Q2.hcardT79_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_37_2 i) (Q2.hfix79_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T79_37 = colFn colCertDiv_79_37_20.D1 (m := 5) from colCertDiv_79_37_20.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T79_37_2 = colFn colCertDiv_79_37_20.D2 (m := 5) from colCertDiv_79_37_20.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_37_20_match


theorem leaf_79_42_0 (hp : 0 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 0 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 0 (transLenTr ⟨42, by decide⟩ 0 hp)) T79_42
      hfix79_42 hinj79_42 hcardT79_42
      (fun i => conj_mem_of_fixedPoints _ _ (T79_42 i) (hfix79_42 i) _)
      ⟨79, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 0 hp) Q2.T79_42_2 Q2.hfix79_42_2 Q2.hinj79_42_2
      Q2.hcardT79_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_42_2 i) (Q2.hfix79_42_2 i) _)
      colCert_79_42_0.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_42_1 (hp : 1 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 1 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 1 (transLenTr ⟨42, by decide⟩ 1 hp)) T79_42
      hfix79_42 hinj79_42 hcardT79_42
      (fun i => conj_mem_of_fixedPoints _ _ (T79_42 i) (hfix79_42 i) _)
      ⟨79, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 1 hp) Q2.T79_42_2 Q2.hfix79_42_2 Q2.hinj79_42_2
      Q2.hcardT79_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_42_2 i) (Q2.hfix79_42_2 i) _)
      colCert_79_42_1.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_42_2 (hp : 2 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 2 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 2 (transLenTr ⟨42, by decide⟩ 2 hp)) T79_42
      hfix79_42 hinj79_42 hcardT79_42
      (fun i => conj_mem_of_fixedPoints _ _ (T79_42 i) (hfix79_42 i) _)
      ⟨79, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 2 hp) Q2.T79_42_2 Q2.hfix79_42_2 Q2.hinj79_42_2
      Q2.hcardT79_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_42_2 i) (Q2.hfix79_42_2 i) _)
      colCert_79_42_2.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_42_3 (hp : 3 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 3 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 3 (transLenTr ⟨42, by decide⟩ 3 hp)) T79_42
      hfix79_42 hinj79_42 hcardT79_42
      (fun i => conj_mem_of_fixedPoints _ _ (T79_42 i) (hfix79_42 i) _)
      ⟨79, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 3 hp) Q2.T79_42_2 Q2.hfix79_42_2 Q2.hinj79_42_2
      Q2.hcardT79_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_42_2 i) (Q2.hfix79_42_2 i) _)
      colCert_79_42_3.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_42_4 (hp : 4 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 4 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 4 (transLenTr ⟨42, by decide⟩ 4 hp)) T79_42
      hfix79_42 hinj79_42 hcardT79_42
      (fun i => conj_mem_of_fixedPoints _ _ (T79_42 i) (hfix79_42 i) _)
      ⟨79, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 4 hp) Q2.T79_42_2 Q2.hfix79_42_2 Q2.hinj79_42_2
      Q2.hcardT79_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_42_2 i) (Q2.hfix79_42_2 i) _)
      colCert_79_42_4.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_42_5 (hp : 5 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 5 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp)) T79_42
      hfix79_42 hinj79_42 hcardT79_42
      (fun i => conj_mem_of_fixedPoints _ _ (T79_42 i) (hfix79_42 i) _)
      ⟨79, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 5 hp) Q2.T79_42_2 Q2.hfix79_42_2 Q2.hinj79_42_2
      Q2.hcardT79_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_42_2 i) (Q2.hfix79_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 5 (transLenTr ⟨42, by decide⟩ 5 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T79_42 = colFn colCertDiv_79_42_5.D1 (m := 5) from colCertDiv_79_42_5.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 5 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T79_42_2 = colFn colCertDiv_79_42_5.D2 (m := 5) from colCertDiv_79_42_5.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_42_5_match


theorem leaf_79_42_10 (hp : 10 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 10 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp)) T79_42
      hfix79_42 hinj79_42 hcardT79_42
      (fun i => conj_mem_of_fixedPoints _ _ (T79_42 i) (hfix79_42 i) _)
      ⟨79, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 10 hp) Q2.T79_42_2 Q2.hfix79_42_2 Q2.hinj79_42_2
      Q2.hcardT79_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_42_2 i) (Q2.hfix79_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 10 (transLenTr ⟨42, by decide⟩ 10 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T79_42 = colFn colCertDiv_79_42_10.D1 (m := 5) from colCertDiv_79_42_10.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 10 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T79_42_2 = colFn colCertDiv_79_42_10.D2 (m := 5) from colCertDiv_79_42_10.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_42_10_match


theorem leaf_79_42_15 (hp : 15 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 15 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp)) T79_42
      hfix79_42 hinj79_42 hcardT79_42
      (fun i => conj_mem_of_fixedPoints _ _ (T79_42 i) (hfix79_42 i) _)
      ⟨79, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 15 hp) Q2.T79_42_2 Q2.hfix79_42_2 Q2.hinj79_42_2
      Q2.hcardT79_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_42_2 i) (Q2.hfix79_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 15 (transLenTr ⟨42, by decide⟩ 15 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T79_42 = colFn colCertDiv_79_42_15.D1 (m := 5) from colCertDiv_79_42_15.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 15 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T79_42_2 = colFn colCertDiv_79_42_15.D2 (m := 5) from colCertDiv_79_42_15.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_42_15_match


theorem leaf_79_42_20 (hp : 20 < (Q2.transData.getD 42 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ 20 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨42, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp)) T79_42
      hfix79_42 hinj79_42 hcardT79_42
      (fun i => conj_mem_of_fixedPoints _ _ (T79_42 i) (hfix79_42 i) _)
      ⟨79, by decide⟩ ⟨42, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨42, by decide⟩ 20 hp) Q2.T79_42_2 Q2.hfix79_42_2 Q2.hinj79_42_2
      Q2.hcardT79_42_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_42_2 i) (Q2.hfix79_42_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨42, by decide⟩ 20 (transLenTr ⟨42, by decide⟩ 20 hp) : ↥(reps ⟨42, by decide⟩)) : Coordinate 1)
        T79_42 = colFn colCertDiv_79_42_20.D1 (m := 5) from colCertDiv_79_42_20.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨42, by decide⟩ 20 hp : ↥(Q2.reps ⟨42, by decide⟩)) : Coordinate 2)
        Q2.T79_42_2 = colFn colCertDiv_79_42_20.D2 (m := 5) from colCertDiv_79_42_20.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_42_20_match


theorem leaf_79_47_0 (hp : 0 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 0 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 0 (transLenTr ⟨47, by decide⟩ 0 hp)) T79_47
      hfix79_47 hinj79_47 hcardT79_47
      (fun i => conj_mem_of_fixedPoints _ _ (T79_47 i) (hfix79_47 i) _)
      ⟨79, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 0 hp) Q2.T79_47_2 Q2.hfix79_47_2 Q2.hinj79_47_2
      Q2.hcardT79_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_47_2 i) (Q2.hfix79_47_2 i) _)
      colCert_79_47_0.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_47_1 (hp : 1 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 1 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 1 (transLenTr ⟨47, by decide⟩ 1 hp)) T79_47
      hfix79_47 hinj79_47 hcardT79_47
      (fun i => conj_mem_of_fixedPoints _ _ (T79_47 i) (hfix79_47 i) _)
      ⟨79, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 1 hp) Q2.T79_47_2 Q2.hfix79_47_2 Q2.hinj79_47_2
      Q2.hcardT79_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_47_2 i) (Q2.hfix79_47_2 i) _)
      colCert_79_47_1.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_47_2 (hp : 2 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 2 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 2 (transLenTr ⟨47, by decide⟩ 2 hp)) T79_47
      hfix79_47 hinj79_47 hcardT79_47
      (fun i => conj_mem_of_fixedPoints _ _ (T79_47 i) (hfix79_47 i) _)
      ⟨79, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 2 hp) Q2.T79_47_2 Q2.hfix79_47_2 Q2.hinj79_47_2
      Q2.hcardT79_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_47_2 i) (Q2.hfix79_47_2 i) _)
      colCert_79_47_2.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_47_3 (hp : 3 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 3 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 3 (transLenTr ⟨47, by decide⟩ 3 hp)) T79_47
      hfix79_47 hinj79_47 hcardT79_47
      (fun i => conj_mem_of_fixedPoints _ _ (T79_47 i) (hfix79_47 i) _)
      ⟨79, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 3 hp) Q2.T79_47_2 Q2.hfix79_47_2 Q2.hinj79_47_2
      Q2.hcardT79_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_47_2 i) (Q2.hfix79_47_2 i) _)
      colCert_79_47_3.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_47_4 (hp : 4 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 4 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 4 (transLenTr ⟨47, by decide⟩ 4 hp)) T79_47
      hfix79_47 hinj79_47 hcardT79_47
      (fun i => conj_mem_of_fixedPoints _ _ (T79_47 i) (hfix79_47 i) _)
      ⟨79, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 4 hp) Q2.T79_47_2 Q2.hfix79_47_2 Q2.hinj79_47_2
      Q2.hcardT79_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_47_2 i) (Q2.hfix79_47_2 i) _)
      colCert_79_47_4.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_47_5 (hp : 5 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 5 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp)) T79_47
      hfix79_47 hinj79_47 hcardT79_47
      (fun i => conj_mem_of_fixedPoints _ _ (T79_47 i) (hfix79_47 i) _)
      ⟨79, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 5 hp) Q2.T79_47_2 Q2.hfix79_47_2 Q2.hinj79_47_2
      Q2.hcardT79_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_47_2 i) (Q2.hfix79_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 5 (transLenTr ⟨47, by decide⟩ 5 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T79_47 = colFn colCertDiv_79_47_5.D1 (m := 5) from colCertDiv_79_47_5.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 5 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T79_47_2 = colFn colCertDiv_79_47_5.D2 (m := 5) from colCertDiv_79_47_5.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_47_5_match


theorem leaf_79_47_10 (hp : 10 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 10 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp)) T79_47
      hfix79_47 hinj79_47 hcardT79_47
      (fun i => conj_mem_of_fixedPoints _ _ (T79_47 i) (hfix79_47 i) _)
      ⟨79, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 10 hp) Q2.T79_47_2 Q2.hfix79_47_2 Q2.hinj79_47_2
      Q2.hcardT79_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_47_2 i) (Q2.hfix79_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 10 (transLenTr ⟨47, by decide⟩ 10 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T79_47 = colFn colCertDiv_79_47_10.D1 (m := 5) from colCertDiv_79_47_10.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 10 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T79_47_2 = colFn colCertDiv_79_47_10.D2 (m := 5) from colCertDiv_79_47_10.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_47_10_match


theorem leaf_79_47_15 (hp : 15 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 15 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp)) T79_47
      hfix79_47 hinj79_47 hcardT79_47
      (fun i => conj_mem_of_fixedPoints _ _ (T79_47 i) (hfix79_47 i) _)
      ⟨79, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 15 hp) Q2.T79_47_2 Q2.hfix79_47_2 Q2.hinj79_47_2
      Q2.hcardT79_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_47_2 i) (Q2.hfix79_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 15 (transLenTr ⟨47, by decide⟩ 15 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T79_47 = colFn colCertDiv_79_47_15.D1 (m := 5) from colCertDiv_79_47_15.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 15 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T79_47_2 = colFn colCertDiv_79_47_15.D2 (m := 5) from colCertDiv_79_47_15.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_47_15_match


theorem leaf_79_47_20 (hp : 20 < (Q2.transData.getD 47 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ 20 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨47, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp)) T79_47
      hfix79_47 hinj79_47 hcardT79_47
      (fun i => conj_mem_of_fixedPoints _ _ (T79_47 i) (hfix79_47 i) _)
      ⟨79, by decide⟩ ⟨47, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨47, by decide⟩ 20 hp) Q2.T79_47_2 Q2.hfix79_47_2 Q2.hinj79_47_2
      Q2.hcardT79_47_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_47_2 i) (Q2.hfix79_47_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨47, by decide⟩ 20 (transLenTr ⟨47, by decide⟩ 20 hp) : ↥(reps ⟨47, by decide⟩)) : Coordinate 1)
        T79_47 = colFn colCertDiv_79_47_20.D1 (m := 5) from colCertDiv_79_47_20.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨47, by decide⟩ 20 hp : ↥(Q2.reps ⟨47, by decide⟩)) : Coordinate 2)
        Q2.T79_47_2 = colFn colCertDiv_79_47_20.D2 (m := 5) from colCertDiv_79_47_20.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_47_20_match


theorem leaf_79_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T79_52
      hfix79_52 hinj79_52 hcardT79_52
      (fun i => conj_mem_of_fixedPoints _ _ (T79_52 i) (hfix79_52 i) _)
      ⟨79, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T79_52_2 Q2.hfix79_52_2 Q2.hinj79_52_2
      Q2.hcardT79_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_52_2 i) (Q2.hfix79_52_2 i) _)
      colCert_79_52_0.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T79_52
      hfix79_52 hinj79_52 hcardT79_52
      (fun i => conj_mem_of_fixedPoints _ _ (T79_52 i) (hfix79_52 i) _)
      ⟨79, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T79_52_2 Q2.hfix79_52_2 Q2.hinj79_52_2
      Q2.hcardT79_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_52_2 i) (Q2.hfix79_52_2 i) _)
      colCert_79_52_1.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T79_52
      hfix79_52 hinj79_52 hcardT79_52
      (fun i => conj_mem_of_fixedPoints _ _ (T79_52 i) (hfix79_52 i) _)
      ⟨79, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T79_52_2 Q2.hfix79_52_2 Q2.hinj79_52_2
      Q2.hcardT79_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_52_2 i) (Q2.hfix79_52_2 i) _)
      colCert_79_52_2.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T79_52
      hfix79_52 hinj79_52 hcardT79_52
      (fun i => conj_mem_of_fixedPoints _ _ (T79_52 i) (hfix79_52 i) _)
      ⟨79, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T79_52_2 Q2.hfix79_52_2 Q2.hinj79_52_2
      Q2.hcardT79_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_52_2 i) (Q2.hfix79_52_2 i) _)
      colCert_79_52_3.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T79_52
      hfix79_52 hinj79_52 hcardT79_52
      (fun i => conj_mem_of_fixedPoints _ _ (T79_52 i) (hfix79_52 i) _)
      ⟨79, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T79_52_2 Q2.hfix79_52_2 Q2.hinj79_52_2
      Q2.hcardT79_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_52_2 i) (Q2.hfix79_52_2 i) _)
      colCert_79_52_4.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T79_52
      hfix79_52 hinj79_52 hcardT79_52
      (fun i => conj_mem_of_fixedPoints _ _ (T79_52 i) (hfix79_52 i) _)
      ⟨79, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T79_52_2 Q2.hfix79_52_2 Q2.hinj79_52_2
      Q2.hcardT79_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_52_2 i) (Q2.hfix79_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T79_52 = colFn colCertDiv_79_52_5.D1 (m := 5) from colCertDiv_79_52_5.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T79_52_2 = colFn colCertDiv_79_52_5.D2 (m := 5) from colCertDiv_79_52_5.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_52_5_match


theorem leaf_79_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T79_52
      hfix79_52 hinj79_52 hcardT79_52
      (fun i => conj_mem_of_fixedPoints _ _ (T79_52 i) (hfix79_52 i) _)
      ⟨79, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T79_52_2 Q2.hfix79_52_2 Q2.hinj79_52_2
      Q2.hcardT79_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_52_2 i) (Q2.hfix79_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T79_52 = colFn colCertDiv_79_52_10.D1 (m := 5) from colCertDiv_79_52_10.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T79_52_2 = colFn colCertDiv_79_52_10.D2 (m := 5) from colCertDiv_79_52_10.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_52_10_match


theorem leaf_79_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T79_52
      hfix79_52 hinj79_52 hcardT79_52
      (fun i => conj_mem_of_fixedPoints _ _ (T79_52 i) (hfix79_52 i) _)
      ⟨79, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T79_52_2 Q2.hfix79_52_2 Q2.hinj79_52_2
      Q2.hcardT79_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_52_2 i) (Q2.hfix79_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T79_52 = colFn colCertDiv_79_52_15.D1 (m := 5) from colCertDiv_79_52_15.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T79_52_2 = colFn colCertDiv_79_52_15.D2 (m := 5) from colCertDiv_79_52_15.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_52_15_match


theorem leaf_79_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨79, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T79_52
      hfix79_52 hinj79_52 hcardT79_52
      (fun i => conj_mem_of_fixedPoints _ _ (T79_52 i) (hfix79_52 i) _)
      ⟨79, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T79_52_2 Q2.hfix79_52_2 Q2.hinj79_52_2
      Q2.hcardT79_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_52_2 i) (Q2.hfix79_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨79, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T79_52 = colFn colCertDiv_79_52_20.D1 (m := 5) from colCertDiv_79_52_20.bind1,
    show colData2 (⟨79, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T79_52_2 = colFn colCertDiv_79_52_20.D2 (m := 5) from colCertDiv_79_52_20.bind2]
  rw [alnId_79 j hj]
  exact fastcode_of_div ⟨79, by decide⟩ _ _ _
    ((alnId_79 j hj) ▸ Q2.listedAt (⟨79, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨79, by decide⟩ : Fin 148) hj hq).1) colCertDiv_79_52_20_match


theorem leaf_79_79_0 (hp : 0 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 0 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 0 (transLenTr ⟨79, by decide⟩ 0 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 0 (transLenTr ⟨79, by decide⟩ 0 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 0 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_0.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_1 (hp : 1 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 1 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 1 (transLenTr ⟨79, by decide⟩ 1 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 1 (transLenTr ⟨79, by decide⟩ 1 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 1 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_1.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_2 (hp : 2 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 2 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 2 (transLenTr ⟨79, by decide⟩ 2 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 2 (transLenTr ⟨79, by decide⟩ 2 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 2 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_2.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_3 (hp : 3 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 3 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 3 (transLenTr ⟨79, by decide⟩ 3 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 3 (transLenTr ⟨79, by decide⟩ 3 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 3 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_3.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_4 (hp : 4 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 4 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 4 (transLenTr ⟨79, by decide⟩ 4 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 4 (transLenTr ⟨79, by decide⟩ 4 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 4 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_4.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_5 (hp : 5 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 5 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 5 (transLenTr ⟨79, by decide⟩ 5 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 5 (transLenTr ⟨79, by decide⟩ 5 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 5 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_5.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_6 (hp : 6 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 6 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 6 (transLenTr ⟨79, by decide⟩ 6 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 6 (transLenTr ⟨79, by decide⟩ 6 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 6 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_6.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_7 (hp : 7 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 7 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 7 (transLenTr ⟨79, by decide⟩ 7 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 7 (transLenTr ⟨79, by decide⟩ 7 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 7 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_7.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_8 (hp : 8 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 8 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 8 (transLenTr ⟨79, by decide⟩ 8 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 8 (transLenTr ⟨79, by decide⟩ 8 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 8 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_8.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_9 (hp : 9 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 9 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 9 (transLenTr ⟨79, by decide⟩ 9 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 9 (transLenTr ⟨79, by decide⟩ 9 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 9 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_9.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_10 (hp : 10 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 10 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 10 (transLenTr ⟨79, by decide⟩ 10 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 10 (transLenTr ⟨79, by decide⟩ 10 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 10 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_10.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_11 (hp : 11 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 11 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 11 (transLenTr ⟨79, by decide⟩ 11 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 11 (transLenTr ⟨79, by decide⟩ 11 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 11 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_11.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_12 (hp : 12 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 12 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 12 (transLenTr ⟨79, by decide⟩ 12 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 12 (transLenTr ⟨79, by decide⟩ 12 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 12 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_12.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_13 (hp : 13 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 13 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 13 (transLenTr ⟨79, by decide⟩ 13 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 13 (transLenTr ⟨79, by decide⟩ 13 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 13 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_13.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_14 (hp : 14 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 14 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 14 (transLenTr ⟨79, by decide⟩ 14 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 14 (transLenTr ⟨79, by decide⟩ 14 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 14 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_14.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_15 (hp : 15 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 15 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 15 (transLenTr ⟨79, by decide⟩ 15 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 15 (transLenTr ⟨79, by decide⟩ 15 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 15 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_15.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_16 (hp : 16 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 16 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 16 (transLenTr ⟨79, by decide⟩ 16 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 16 (transLenTr ⟨79, by decide⟩ 16 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 16 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_16.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_17 (hp : 17 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 17 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 17 (transLenTr ⟨79, by decide⟩ 17 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 17 (transLenTr ⟨79, by decide⟩ 17 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 17 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_17.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_18 (hp : 18 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 18 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 18 (transLenTr ⟨79, by decide⟩ 18 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 18 (transLenTr ⟨79, by decide⟩ 18 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 18 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_18.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_19 (hp : 19 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 19 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 19 (transLenTr ⟨79, by decide⟩ 19 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 19 (transLenTr ⟨79, by decide⟩ 19 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 19 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_19.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_20 (hp : 20 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 20 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 20 (transLenTr ⟨79, by decide⟩ 20 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 20 (transLenTr ⟨79, by decide⟩ 20 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 20 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_20.hD ?_).symm
  rw [alnId_79 j hj]


end LeanDring.P5Presentation
