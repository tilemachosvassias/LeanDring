/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColRestCheap.C108
import LeanDring.P5.Data.ColRestCheap.C109
import LeanDring.P5.Data.ColRestCheap.C110
import LeanDring.P5.Data.ColRestCheap.C111
import LeanDring.P5.Data.ColRestCheap.C112
import LeanDring.P5.Data.ColTau.C002
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk03

/-! # Stage-5 leaves, chunk 48 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_147_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T147_5
      hfix147_5 hinj147_5 hcardT147_5
      (fun i => conj_mem_of_fixedPoints _ _ (T147_5 i) (hfix147_5 i) _)
      ⟨147, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T147_5_2 Q2.hfix147_5_2 Q2.hinj147_5_2
      Q2.hcardT147_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_5_2 i) (Q2.hfix147_5_2 i) _)
      colCert_147_5_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T147_5
      hfix147_5 hinj147_5 hcardT147_5
      (fun i => conj_mem_of_fixedPoints _ _ (T147_5 i) (hfix147_5 i) _)
      ⟨147, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T147_5_2 Q2.hfix147_5_2 Q2.hinj147_5_2
      Q2.hcardT147_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_5_2 i) (Q2.hfix147_5_2 i) _)
      colCert_147_5_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T147_5
      hfix147_5 hinj147_5 hcardT147_5
      (fun i => conj_mem_of_fixedPoints _ _ (T147_5 i) (hfix147_5 i) _)
      ⟨147, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T147_5_2 Q2.hfix147_5_2 Q2.hinj147_5_2
      Q2.hcardT147_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_5_2 i) (Q2.hfix147_5_2 i) _)
      colCert_147_5_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T147_5
      hfix147_5 hinj147_5 hcardT147_5
      (fun i => conj_mem_of_fixedPoints _ _ (T147_5 i) (hfix147_5 i) _)
      ⟨147, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T147_5_2 Q2.hfix147_5_2 Q2.hinj147_5_2
      Q2.hcardT147_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_5_2 i) (Q2.hfix147_5_2 i) _)
      colCert_147_5_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T147_5
      hfix147_5 hinj147_5 hcardT147_5
      (fun i => conj_mem_of_fixedPoints _ _ (T147_5 i) (hfix147_5 i) _)
      ⟨147, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T147_5_2 Q2.hfix147_5_2 Q2.hinj147_5_2
      Q2.hcardT147_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_5_2 i) (Q2.hfix147_5_2 i) _)
      colCert_147_5_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T147_6
      hfix147_6 hinj147_6 hcardT147_6
      (fun i => conj_mem_of_fixedPoints _ _ (T147_6 i) (hfix147_6 i) _)
      ⟨147, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T147_6_2 Q2.hfix147_6_2 Q2.hinj147_6_2
      Q2.hcardT147_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_6_2 i) (Q2.hfix147_6_2 i) _)
      colCert_147_6_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T147_6
      hfix147_6 hinj147_6 hcardT147_6
      (fun i => conj_mem_of_fixedPoints _ _ (T147_6 i) (hfix147_6 i) _)
      ⟨147, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T147_6_2 Q2.hfix147_6_2 Q2.hinj147_6_2
      Q2.hcardT147_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_6_2 i) (Q2.hfix147_6_2 i) _)
      colCert_147_6_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T147_6
      hfix147_6 hinj147_6 hcardT147_6
      (fun i => conj_mem_of_fixedPoints _ _ (T147_6 i) (hfix147_6 i) _)
      ⟨147, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T147_6_2 Q2.hfix147_6_2 Q2.hinj147_6_2
      Q2.hcardT147_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_6_2 i) (Q2.hfix147_6_2 i) _)
      colCert_147_6_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T147_6
      hfix147_6 hinj147_6 hcardT147_6
      (fun i => conj_mem_of_fixedPoints _ _ (T147_6 i) (hfix147_6 i) _)
      ⟨147, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T147_6_2 Q2.hfix147_6_2 Q2.hinj147_6_2
      Q2.hcardT147_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_6_2 i) (Q2.hfix147_6_2 i) _)
      colCert_147_6_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T147_6
      hfix147_6 hinj147_6 hcardT147_6
      (fun i => conj_mem_of_fixedPoints _ _ (T147_6 i) (hfix147_6 i) _)
      ⟨147, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T147_6_2 Q2.hfix147_6_2 Q2.hinj147_6_2
      Q2.hcardT147_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_6_2 i) (Q2.hfix147_6_2 i) _)
      colCert_147_6_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T147_7
      hfix147_7 hinj147_7 hcardT147_7
      (fun i => conj_mem_of_fixedPoints _ _ (T147_7 i) (hfix147_7 i) _)
      ⟨147, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T147_7_2 Q2.hfix147_7_2 Q2.hinj147_7_2
      Q2.hcardT147_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_7_2 i) (Q2.hfix147_7_2 i) _)
      colCert_147_7_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T147_7
      hfix147_7 hinj147_7 hcardT147_7
      (fun i => conj_mem_of_fixedPoints _ _ (T147_7 i) (hfix147_7 i) _)
      ⟨147, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T147_7_2 Q2.hfix147_7_2 Q2.hinj147_7_2
      Q2.hcardT147_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_7_2 i) (Q2.hfix147_7_2 i) _)
      colCert_147_7_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T147_7
      hfix147_7 hinj147_7 hcardT147_7
      (fun i => conj_mem_of_fixedPoints _ _ (T147_7 i) (hfix147_7 i) _)
      ⟨147, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T147_7_2 Q2.hfix147_7_2 Q2.hinj147_7_2
      Q2.hcardT147_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_7_2 i) (Q2.hfix147_7_2 i) _)
      colCert_147_7_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T147_7
      hfix147_7 hinj147_7 hcardT147_7
      (fun i => conj_mem_of_fixedPoints _ _ (T147_7 i) (hfix147_7 i) _)
      ⟨147, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T147_7_2 Q2.hfix147_7_2 Q2.hinj147_7_2
      Q2.hcardT147_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_7_2 i) (Q2.hfix147_7_2 i) _)
      colCert_147_7_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T147_7
      hfix147_7 hinj147_7 hcardT147_7
      (fun i => conj_mem_of_fixedPoints _ _ (T147_7 i) (hfix147_7 i) _)
      ⟨147, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T147_7_2 Q2.hfix147_7_2 Q2.hinj147_7_2
      Q2.hcardT147_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_7_2 i) (Q2.hfix147_7_2 i) _)
      colCert_147_7_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T147_8
      hfix147_8 hinj147_8 hcardT147_8
      (fun i => conj_mem_of_fixedPoints _ _ (T147_8 i) (hfix147_8 i) _)
      ⟨147, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T147_8_2 Q2.hfix147_8_2 Q2.hinj147_8_2
      Q2.hcardT147_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_8_2 i) (Q2.hfix147_8_2 i) _)
      colCert_147_8_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T147_8
      hfix147_8 hinj147_8 hcardT147_8
      (fun i => conj_mem_of_fixedPoints _ _ (T147_8 i) (hfix147_8 i) _)
      ⟨147, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T147_8_2 Q2.hfix147_8_2 Q2.hinj147_8_2
      Q2.hcardT147_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_8_2 i) (Q2.hfix147_8_2 i) _)
      colCert_147_8_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T147_8
      hfix147_8 hinj147_8 hcardT147_8
      (fun i => conj_mem_of_fixedPoints _ _ (T147_8 i) (hfix147_8 i) _)
      ⟨147, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T147_8_2 Q2.hfix147_8_2 Q2.hinj147_8_2
      Q2.hcardT147_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_8_2 i) (Q2.hfix147_8_2 i) _)
      colCert_147_8_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T147_8
      hfix147_8 hinj147_8 hcardT147_8
      (fun i => conj_mem_of_fixedPoints _ _ (T147_8 i) (hfix147_8 i) _)
      ⟨147, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T147_8_2 Q2.hfix147_8_2 Q2.hinj147_8_2
      Q2.hcardT147_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_8_2 i) (Q2.hfix147_8_2 i) _)
      colCert_147_8_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T147_8
      hfix147_8 hinj147_8 hcardT147_8
      (fun i => conj_mem_of_fixedPoints _ _ (T147_8 i) (hfix147_8 i) _)
      ⟨147, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T147_8_2 Q2.hfix147_8_2 Q2.hinj147_8_2
      Q2.hcardT147_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_8_2 i) (Q2.hfix147_8_2 i) _)
      colCert_147_8_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T147_9
      hfix147_9 hinj147_9 hcardT147_9
      (fun i => conj_mem_of_fixedPoints _ _ (T147_9 i) (hfix147_9 i) _)
      ⟨147, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T147_9_2 Q2.hfix147_9_2 Q2.hinj147_9_2
      Q2.hcardT147_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_9_2 i) (Q2.hfix147_9_2 i) _)
      colCert_147_9_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T147_9
      hfix147_9 hinj147_9 hcardT147_9
      (fun i => conj_mem_of_fixedPoints _ _ (T147_9 i) (hfix147_9 i) _)
      ⟨147, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T147_9_2 Q2.hfix147_9_2 Q2.hinj147_9_2
      Q2.hcardT147_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_9_2 i) (Q2.hfix147_9_2 i) _)
      colCert_147_9_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T147_9
      hfix147_9 hinj147_9 hcardT147_9
      (fun i => conj_mem_of_fixedPoints _ _ (T147_9 i) (hfix147_9 i) _)
      ⟨147, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T147_9_2 Q2.hfix147_9_2 Q2.hinj147_9_2
      Q2.hcardT147_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_9_2 i) (Q2.hfix147_9_2 i) _)
      colCert_147_9_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T147_9
      hfix147_9 hinj147_9 hcardT147_9
      (fun i => conj_mem_of_fixedPoints _ _ (T147_9 i) (hfix147_9 i) _)
      ⟨147, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T147_9_2 Q2.hfix147_9_2 Q2.hinj147_9_2
      Q2.hcardT147_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_9_2 i) (Q2.hfix147_9_2 i) _)
      colCert_147_9_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T147_9
      hfix147_9 hinj147_9 hcardT147_9
      (fun i => conj_mem_of_fixedPoints _ _ (T147_9 i) (hfix147_9 i) _)
      ⟨147, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T147_9_2 Q2.hfix147_9_2 Q2.hinj147_9_2
      Q2.hcardT147_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_9_2 i) (Q2.hfix147_9_2 i) _)
      colCert_147_9_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T147_10
      hfix147_10 hinj147_10 hcardT147_10
      (fun i => conj_mem_of_fixedPoints _ _ (T147_10 i) (hfix147_10 i) _)
      ⟨147, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T147_10_2 Q2.hfix147_10_2 Q2.hinj147_10_2
      Q2.hcardT147_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_10_2 i) (Q2.hfix147_10_2 i) _)
      colCert_147_10_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T147_10
      hfix147_10 hinj147_10 hcardT147_10
      (fun i => conj_mem_of_fixedPoints _ _ (T147_10 i) (hfix147_10 i) _)
      ⟨147, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T147_10_2 Q2.hfix147_10_2 Q2.hinj147_10_2
      Q2.hcardT147_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_10_2 i) (Q2.hfix147_10_2 i) _)
      colCert_147_10_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T147_10
      hfix147_10 hinj147_10 hcardT147_10
      (fun i => conj_mem_of_fixedPoints _ _ (T147_10 i) (hfix147_10 i) _)
      ⟨147, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T147_10_2 Q2.hfix147_10_2 Q2.hinj147_10_2
      Q2.hcardT147_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_10_2 i) (Q2.hfix147_10_2 i) _)
      colCert_147_10_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T147_10
      hfix147_10 hinj147_10 hcardT147_10
      (fun i => conj_mem_of_fixedPoints _ _ (T147_10 i) (hfix147_10 i) _)
      ⟨147, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T147_10_2 Q2.hfix147_10_2 Q2.hinj147_10_2
      Q2.hcardT147_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_10_2 i) (Q2.hfix147_10_2 i) _)
      colCert_147_10_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T147_10
      hfix147_10 hinj147_10 hcardT147_10
      (fun i => conj_mem_of_fixedPoints _ _ (T147_10 i) (hfix147_10 i) _)
      ⟨147, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T147_10_2 Q2.hfix147_10_2 Q2.hinj147_10_2
      Q2.hcardT147_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_10_2 i) (Q2.hfix147_10_2 i) _)
      colCert_147_10_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T147_11
      hfix147_11 hinj147_11 hcardT147_11
      (fun i => conj_mem_of_fixedPoints _ _ (T147_11 i) (hfix147_11 i) _)
      ⟨147, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T147_11_2 Q2.hfix147_11_2 Q2.hinj147_11_2
      Q2.hcardT147_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_11_2 i) (Q2.hfix147_11_2 i) _)
      colCert_147_11_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T147_11
      hfix147_11 hinj147_11 hcardT147_11
      (fun i => conj_mem_of_fixedPoints _ _ (T147_11 i) (hfix147_11 i) _)
      ⟨147, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T147_11_2 Q2.hfix147_11_2 Q2.hinj147_11_2
      Q2.hcardT147_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_11_2 i) (Q2.hfix147_11_2 i) _)
      colCert_147_11_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T147_11
      hfix147_11 hinj147_11 hcardT147_11
      (fun i => conj_mem_of_fixedPoints _ _ (T147_11 i) (hfix147_11 i) _)
      ⟨147, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T147_11_2 Q2.hfix147_11_2 Q2.hinj147_11_2
      Q2.hcardT147_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_11_2 i) (Q2.hfix147_11_2 i) _)
      colCert_147_11_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T147_11
      hfix147_11 hinj147_11 hcardT147_11
      (fun i => conj_mem_of_fixedPoints _ _ (T147_11 i) (hfix147_11 i) _)
      ⟨147, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T147_11_2 Q2.hfix147_11_2 Q2.hinj147_11_2
      Q2.hcardT147_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_11_2 i) (Q2.hfix147_11_2 i) _)
      colCert_147_11_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T147_11
      hfix147_11 hinj147_11 hcardT147_11
      (fun i => conj_mem_of_fixedPoints _ _ (T147_11 i) (hfix147_11 i) _)
      ⟨147, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T147_11_2 Q2.hfix147_11_2 Q2.hinj147_11_2
      Q2.hcardT147_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_11_2 i) (Q2.hfix147_11_2 i) _)
      colCert_147_11_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T147_12
      hfix147_12 hinj147_12 hcardT147_12
      (fun i => conj_mem_of_fixedPoints _ _ (T147_12 i) (hfix147_12 i) _)
      ⟨147, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T147_12_2 Q2.hfix147_12_2 Q2.hinj147_12_2
      Q2.hcardT147_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_12_2 i) (Q2.hfix147_12_2 i) _)
      colCert_147_12_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T147_12
      hfix147_12 hinj147_12 hcardT147_12
      (fun i => conj_mem_of_fixedPoints _ _ (T147_12 i) (hfix147_12 i) _)
      ⟨147, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T147_12_2 Q2.hfix147_12_2 Q2.hinj147_12_2
      Q2.hcardT147_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_12_2 i) (Q2.hfix147_12_2 i) _)
      colCert_147_12_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T147_12
      hfix147_12 hinj147_12 hcardT147_12
      (fun i => conj_mem_of_fixedPoints _ _ (T147_12 i) (hfix147_12 i) _)
      ⟨147, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T147_12_2 Q2.hfix147_12_2 Q2.hinj147_12_2
      Q2.hcardT147_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_12_2 i) (Q2.hfix147_12_2 i) _)
      colCert_147_12_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T147_12
      hfix147_12 hinj147_12 hcardT147_12
      (fun i => conj_mem_of_fixedPoints _ _ (T147_12 i) (hfix147_12 i) _)
      ⟨147, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T147_12_2 Q2.hfix147_12_2 Q2.hinj147_12_2
      Q2.hcardT147_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_12_2 i) (Q2.hfix147_12_2 i) _)
      colCert_147_12_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T147_12
      hfix147_12 hinj147_12 hcardT147_12
      (fun i => conj_mem_of_fixedPoints _ _ (T147_12 i) (hfix147_12 i) _)
      ⟨147, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T147_12_2 Q2.hfix147_12_2 Q2.hinj147_12_2
      Q2.hcardT147_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_12_2 i) (Q2.hfix147_12_2 i) _)
      colCert_147_12_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_0 (hp : 0 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 0 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_1 (hp : 1 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 1 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_2 (hp : 2 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 2 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_3 (hp : 3 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 3 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_4 (hp : 4 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 4 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_5 (hp : 5 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 5 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T147_13 = colFn colCertDiv_147_13_5.D1 (m := 1) from colCertDiv_147_13_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 5 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T147_13_2 = colFn colCertDiv_147_13_5.D2 (m := 1) from colCertDiv_147_13_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_13_5_tau_match


theorem leaf_147_13_6 (hp : 6 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 6 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T147_13 = colFn colCertDiv_147_13_6.D1 (m := 1) from colCertDiv_147_13_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 6 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T147_13_2 = colFn colCertDiv_147_13_6.D2 (m := 1) from colCertDiv_147_13_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_13_6_tau_match


theorem leaf_147_13_7 (hp : 7 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 7 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T147_13 = colFn colCertDiv_147_13_7.D1 (m := 1) from colCertDiv_147_13_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 7 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T147_13_2 = colFn colCertDiv_147_13_7.D2 (m := 1) from colCertDiv_147_13_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_13_7_tau_match


theorem leaf_147_13_8 (hp : 8 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 8 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T147_13 = colFn colCertDiv_147_13_8.D1 (m := 1) from colCertDiv_147_13_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 8 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T147_13_2 = colFn colCertDiv_147_13_8.D2 (m := 1) from colCertDiv_147_13_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_tau ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_13_8_tau_match


theorem leaf_147_13_9 (hp : 9 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 9 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_10 (hp : 10 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 10 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_11 (hp : 11 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 11 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_12 (hp : 12 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 12 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_13 (hp : 13 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 13 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_14 (hp : 14 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 14 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_15 (hp : 15 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 15 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_16 (hp : 16 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 16 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_17 (hp : 17 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 17 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_18 (hp : 18 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 18 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_19 (hp : 19 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 19 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_20 (hp : 20 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 20 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_21 (hp : 21 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 21 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_22 (hp : 22 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 22 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_23 (hp : 23 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 23 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_13_24 (hp : 24 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp)) T147_13
      hfix147_13 hinj147_13 hcardT147_13
      (fun i => conj_mem_of_fixedPoints _ _ (T147_13 i) (hfix147_13 i) _)
      ⟨147, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 24 hp) Q2.T147_13_2 Q2.hfix147_13_2 Q2.hinj147_13_2
      Q2.hcardT147_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_13_2 i) (Q2.hfix147_13_2 i) _)
      colCert_147_13_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_0 (hp : 0 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 0 (transLenTr ⟨14, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 0 (transLenTr ⟨14, by decide⟩ 0 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 0 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_1 (hp : 1 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 1 (transLenTr ⟨14, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 1 (transLenTr ⟨14, by decide⟩ 1 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 1 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_2 (hp : 2 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 2 (transLenTr ⟨14, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 2 (transLenTr ⟨14, by decide⟩ 2 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 2 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_3 (hp : 3 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 3 (transLenTr ⟨14, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 3 (transLenTr ⟨14, by decide⟩ 3 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 3 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_4 (hp : 4 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 4 (transLenTr ⟨14, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 4 (transLenTr ⟨14, by decide⟩ 4 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 4 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_5 (hp : 5 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 5 (transLenTr ⟨14, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 5 (transLenTr ⟨14, by decide⟩ 5 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 5 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_6 (hp : 6 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 6 (transLenTr ⟨14, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 6 (transLenTr ⟨14, by decide⟩ 6 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 6 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_7 (hp : 7 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 7 (transLenTr ⟨14, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 7 (transLenTr ⟨14, by decide⟩ 7 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 7 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_8 (hp : 8 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 8 (transLenTr ⟨14, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 8 (transLenTr ⟨14, by decide⟩ 8 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 8 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_9 (hp : 9 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 9 (transLenTr ⟨14, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 9 (transLenTr ⟨14, by decide⟩ 9 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 9 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_10 (hp : 10 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 10 (transLenTr ⟨14, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 10 (transLenTr ⟨14, by decide⟩ 10 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 10 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_11 (hp : 11 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 11 (transLenTr ⟨14, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 11 (transLenTr ⟨14, by decide⟩ 11 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 11 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_12 (hp : 12 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 12 (transLenTr ⟨14, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 12 (transLenTr ⟨14, by decide⟩ 12 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 12 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_13 (hp : 13 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 13 (transLenTr ⟨14, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 13 (transLenTr ⟨14, by decide⟩ 13 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 13 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_14 (hp : 14 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 14 (transLenTr ⟨14, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 14 (transLenTr ⟨14, by decide⟩ 14 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 14 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_15 (hp : 15 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 15 (transLenTr ⟨14, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 15 (transLenTr ⟨14, by decide⟩ 15 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 15 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_16 (hp : 16 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 16 (transLenTr ⟨14, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 16 (transLenTr ⟨14, by decide⟩ 16 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 16 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_17 (hp : 17 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 17 (transLenTr ⟨14, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 17 (transLenTr ⟨14, by decide⟩ 17 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 17 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_18 (hp : 18 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 18 (transLenTr ⟨14, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 18 (transLenTr ⟨14, by decide⟩ 18 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 18 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_19 (hp : 19 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 19 (transLenTr ⟨14, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 19 (transLenTr ⟨14, by decide⟩ 19 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 19 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_20 (hp : 20 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 20 (transLenTr ⟨14, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 20 (transLenTr ⟨14, by decide⟩ 20 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 20 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_21 (hp : 21 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 21 (transLenTr ⟨14, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 21 (transLenTr ⟨14, by decide⟩ 21 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 21 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_22 (hp : 22 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 22 (transLenTr ⟨14, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 22 (transLenTr ⟨14, by decide⟩ 22 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 22 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_23 (hp : 23 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 23 (transLenTr ⟨14, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 23 (transLenTr ⟨14, by decide⟩ 23 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 23 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_14_24 (hp : 24 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 24 (transLenTr ⟨14, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 24 (transLenTr ⟨14, by decide⟩ 24 hp)) T147_14
      hfix147_14 hinj147_14 hcardT147_14
      (fun i => conj_mem_of_fixedPoints _ _ (T147_14 i) (hfix147_14 i) _)
      ⟨147, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 24 hp) Q2.T147_14_2 Q2.hfix147_14_2 Q2.hinj147_14_2
      Q2.hcardT147_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_14_2 i) (Q2.hfix147_14_2 i) _)
      colCert_147_14_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_0 (hp : 0 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 0 (transLenTr ⟨15, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 0 (transLenTr ⟨15, by decide⟩ 0 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 0 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_1 (hp : 1 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 1 (transLenTr ⟨15, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 1 (transLenTr ⟨15, by decide⟩ 1 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 1 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_2 (hp : 2 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 2 (transLenTr ⟨15, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 2 (transLenTr ⟨15, by decide⟩ 2 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 2 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_3 (hp : 3 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 3 (transLenTr ⟨15, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 3 (transLenTr ⟨15, by decide⟩ 3 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 3 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_4 (hp : 4 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 4 (transLenTr ⟨15, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 4 (transLenTr ⟨15, by decide⟩ 4 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 4 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_5 (hp : 5 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 5 (transLenTr ⟨15, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 5 (transLenTr ⟨15, by decide⟩ 5 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 5 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_6 (hp : 6 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 6 (transLenTr ⟨15, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 6 (transLenTr ⟨15, by decide⟩ 6 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 6 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_7 (hp : 7 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 7 (transLenTr ⟨15, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 7 (transLenTr ⟨15, by decide⟩ 7 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 7 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_8 (hp : 8 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 8 (transLenTr ⟨15, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 8 (transLenTr ⟨15, by decide⟩ 8 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 8 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_9 (hp : 9 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 9 (transLenTr ⟨15, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 9 (transLenTr ⟨15, by decide⟩ 9 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 9 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_10 (hp : 10 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 10 (transLenTr ⟨15, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 10 (transLenTr ⟨15, by decide⟩ 10 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 10 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_11 (hp : 11 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 11 (transLenTr ⟨15, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 11 (transLenTr ⟨15, by decide⟩ 11 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 11 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_12 (hp : 12 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 12 (transLenTr ⟨15, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 12 (transLenTr ⟨15, by decide⟩ 12 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 12 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_13 (hp : 13 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 13 (transLenTr ⟨15, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 13 (transLenTr ⟨15, by decide⟩ 13 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 13 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_14 (hp : 14 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 14 (transLenTr ⟨15, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 14 (transLenTr ⟨15, by decide⟩ 14 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 14 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_15 (hp : 15 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 15 (transLenTr ⟨15, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 15 (transLenTr ⟨15, by decide⟩ 15 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 15 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_16 (hp : 16 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 16 (transLenTr ⟨15, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 16 (transLenTr ⟨15, by decide⟩ 16 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 16 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_17 (hp : 17 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 17 (transLenTr ⟨15, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 17 (transLenTr ⟨15, by decide⟩ 17 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 17 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_18 (hp : 18 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 18 (transLenTr ⟨15, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 18 (transLenTr ⟨15, by decide⟩ 18 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 18 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_19 (hp : 19 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 19 (transLenTr ⟨15, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 19 (transLenTr ⟨15, by decide⟩ 19 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 19 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_20 (hp : 20 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 20 (transLenTr ⟨15, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 20 (transLenTr ⟨15, by decide⟩ 20 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 20 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_21 (hp : 21 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 21 (transLenTr ⟨15, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 21 (transLenTr ⟨15, by decide⟩ 21 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 21 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_22 (hp : 22 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 22 (transLenTr ⟨15, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 22 (transLenTr ⟨15, by decide⟩ 22 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 22 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_23 (hp : 23 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 23 (transLenTr ⟨15, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 23 (transLenTr ⟨15, by decide⟩ 23 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 23 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_15_24 (hp : 24 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 24 (transLenTr ⟨15, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 24 (transLenTr ⟨15, by decide⟩ 24 hp)) T147_15
      hfix147_15 hinj147_15 hcardT147_15
      (fun i => conj_mem_of_fixedPoints _ _ (T147_15 i) (hfix147_15 i) _)
      ⟨147, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 24 hp) Q2.T147_15_2 Q2.hfix147_15_2 Q2.hinj147_15_2
      Q2.hcardT147_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_15_2 i) (Q2.hfix147_15_2 i) _)
      colCert_147_15_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_0 (hp : 0 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 0 (transLenTr ⟨16, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 0 (transLenTr ⟨16, by decide⟩ 0 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 0 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_1 (hp : 1 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 1 (transLenTr ⟨16, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 1 (transLenTr ⟨16, by decide⟩ 1 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 1 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_2 (hp : 2 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 2 (transLenTr ⟨16, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 2 (transLenTr ⟨16, by decide⟩ 2 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 2 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_3 (hp : 3 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 3 (transLenTr ⟨16, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 3 (transLenTr ⟨16, by decide⟩ 3 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 3 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_4 (hp : 4 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 4 (transLenTr ⟨16, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 4 (transLenTr ⟨16, by decide⟩ 4 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 4 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_5 (hp : 5 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 5 (transLenTr ⟨16, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 5 (transLenTr ⟨16, by decide⟩ 5 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 5 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_6 (hp : 6 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 6 (transLenTr ⟨16, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 6 (transLenTr ⟨16, by decide⟩ 6 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 6 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_7 (hp : 7 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 7 (transLenTr ⟨16, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 7 (transLenTr ⟨16, by decide⟩ 7 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 7 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_8 (hp : 8 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 8 (transLenTr ⟨16, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 8 (transLenTr ⟨16, by decide⟩ 8 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 8 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_9 (hp : 9 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 9 (transLenTr ⟨16, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 9 (transLenTr ⟨16, by decide⟩ 9 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 9 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_10 (hp : 10 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 10 (transLenTr ⟨16, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 10 (transLenTr ⟨16, by decide⟩ 10 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 10 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_11 (hp : 11 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 11 (transLenTr ⟨16, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 11 (transLenTr ⟨16, by decide⟩ 11 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 11 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_12 (hp : 12 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 12 (transLenTr ⟨16, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 12 (transLenTr ⟨16, by decide⟩ 12 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 12 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_13 (hp : 13 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 13 (transLenTr ⟨16, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 13 (transLenTr ⟨16, by decide⟩ 13 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 13 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_14 (hp : 14 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 14 (transLenTr ⟨16, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 14 (transLenTr ⟨16, by decide⟩ 14 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 14 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_15 (hp : 15 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 15 (transLenTr ⟨16, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 15 (transLenTr ⟨16, by decide⟩ 15 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 15 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_16 (hp : 16 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 16 (transLenTr ⟨16, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 16 (transLenTr ⟨16, by decide⟩ 16 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 16 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_17 (hp : 17 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 17 (transLenTr ⟨16, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 17 (transLenTr ⟨16, by decide⟩ 17 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 17 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_18 (hp : 18 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 18 (transLenTr ⟨16, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 18 (transLenTr ⟨16, by decide⟩ 18 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 18 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_19 (hp : 19 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 19 (transLenTr ⟨16, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 19 (transLenTr ⟨16, by decide⟩ 19 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 19 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_20 (hp : 20 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 20 (transLenTr ⟨16, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 20 (transLenTr ⟨16, by decide⟩ 20 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 20 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_21 (hp : 21 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 21 (transLenTr ⟨16, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 21 (transLenTr ⟨16, by decide⟩ 21 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 21 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_22 (hp : 22 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 22 (transLenTr ⟨16, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 22 (transLenTr ⟨16, by decide⟩ 22 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 22 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_23 (hp : 23 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 23 (transLenTr ⟨16, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 23 (transLenTr ⟨16, by decide⟩ 23 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 23 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_16_24 (hp : 24 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 24 (transLenTr ⟨16, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 24 (transLenTr ⟨16, by decide⟩ 24 hp)) T147_16
      hfix147_16 hinj147_16 hcardT147_16
      (fun i => conj_mem_of_fixedPoints _ _ (T147_16 i) (hfix147_16 i) _)
      ⟨147, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 24 hp) Q2.T147_16_2 Q2.hfix147_16_2 Q2.hinj147_16_2
      Q2.hcardT147_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_16_2 i) (Q2.hfix147_16_2 i) _)
      colCert_147_16_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_0 (hp : 0 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 0 (transLenTr ⟨17, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 0 (transLenTr ⟨17, by decide⟩ 0 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 0 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_1 (hp : 1 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 1 (transLenTr ⟨17, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 1 (transLenTr ⟨17, by decide⟩ 1 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 1 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_2 (hp : 2 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 2 (transLenTr ⟨17, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 2 (transLenTr ⟨17, by decide⟩ 2 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 2 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_3 (hp : 3 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 3 (transLenTr ⟨17, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 3 (transLenTr ⟨17, by decide⟩ 3 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 3 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_4 (hp : 4 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 4 (transLenTr ⟨17, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 4 (transLenTr ⟨17, by decide⟩ 4 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 4 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_5 (hp : 5 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 5 (transLenTr ⟨17, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 5 (transLenTr ⟨17, by decide⟩ 5 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 5 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_6 (hp : 6 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 6 (transLenTr ⟨17, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 6 (transLenTr ⟨17, by decide⟩ 6 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 6 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_7 (hp : 7 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 7 (transLenTr ⟨17, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 7 (transLenTr ⟨17, by decide⟩ 7 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 7 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_8 (hp : 8 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 8 (transLenTr ⟨17, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 8 (transLenTr ⟨17, by decide⟩ 8 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 8 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_9 (hp : 9 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 9 (transLenTr ⟨17, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 9 (transLenTr ⟨17, by decide⟩ 9 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 9 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_10 (hp : 10 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 10 (transLenTr ⟨17, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 10 (transLenTr ⟨17, by decide⟩ 10 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 10 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_11 (hp : 11 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 11 (transLenTr ⟨17, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 11 (transLenTr ⟨17, by decide⟩ 11 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 11 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_12 (hp : 12 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 12 (transLenTr ⟨17, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 12 (transLenTr ⟨17, by decide⟩ 12 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 12 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_13 (hp : 13 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 13 (transLenTr ⟨17, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 13 (transLenTr ⟨17, by decide⟩ 13 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 13 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_14 (hp : 14 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 14 (transLenTr ⟨17, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 14 (transLenTr ⟨17, by decide⟩ 14 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 14 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_15 (hp : 15 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 15 (transLenTr ⟨17, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 15 (transLenTr ⟨17, by decide⟩ 15 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 15 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_16 (hp : 16 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 16 (transLenTr ⟨17, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 16 (transLenTr ⟨17, by decide⟩ 16 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 16 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_17 (hp : 17 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 17 (transLenTr ⟨17, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 17 (transLenTr ⟨17, by decide⟩ 17 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 17 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_18 (hp : 18 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 18 (transLenTr ⟨17, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 18 (transLenTr ⟨17, by decide⟩ 18 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 18 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_19 (hp : 19 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 19 (transLenTr ⟨17, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 19 (transLenTr ⟨17, by decide⟩ 19 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 19 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_20 (hp : 20 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 20 (transLenTr ⟨17, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 20 (transLenTr ⟨17, by decide⟩ 20 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 20 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_21 (hp : 21 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 21 (transLenTr ⟨17, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 21 (transLenTr ⟨17, by decide⟩ 21 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 21 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_22 (hp : 22 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 22 (transLenTr ⟨17, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 22 (transLenTr ⟨17, by decide⟩ 22 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 22 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_23 (hp : 23 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 23 (transLenTr ⟨17, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 23 (transLenTr ⟨17, by decide⟩ 23 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 23 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_17_24 (hp : 24 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 24 (transLenTr ⟨17, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 24 (transLenTr ⟨17, by decide⟩ 24 hp)) T147_17
      hfix147_17 hinj147_17 hcardT147_17
      (fun i => conj_mem_of_fixedPoints _ _ (T147_17 i) (hfix147_17 i) _)
      ⟨147, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 24 hp) Q2.T147_17_2 Q2.hfix147_17_2 Q2.hinj147_17_2
      Q2.hcardT147_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_17_2 i) (Q2.hfix147_17_2 i) _)
      colCert_147_17_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_0 (hp : 0 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 0 (transLenTr ⟨18, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 0 (transLenTr ⟨18, by decide⟩ 0 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 0 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_1 (hp : 1 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 1 (transLenTr ⟨18, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 1 (transLenTr ⟨18, by decide⟩ 1 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 1 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_2 (hp : 2 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 2 (transLenTr ⟨18, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 2 (transLenTr ⟨18, by decide⟩ 2 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 2 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_3 (hp : 3 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 3 (transLenTr ⟨18, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 3 (transLenTr ⟨18, by decide⟩ 3 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 3 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_4 (hp : 4 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 4 (transLenTr ⟨18, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 4 (transLenTr ⟨18, by decide⟩ 4 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 4 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_5 (hp : 5 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 5 (transLenTr ⟨18, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 5 (transLenTr ⟨18, by decide⟩ 5 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 5 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_6 (hp : 6 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 6 (transLenTr ⟨18, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 6 (transLenTr ⟨18, by decide⟩ 6 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 6 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_7 (hp : 7 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 7 (transLenTr ⟨18, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 7 (transLenTr ⟨18, by decide⟩ 7 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 7 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_8 (hp : 8 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 8 (transLenTr ⟨18, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 8 (transLenTr ⟨18, by decide⟩ 8 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 8 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_9 (hp : 9 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 9 (transLenTr ⟨18, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 9 (transLenTr ⟨18, by decide⟩ 9 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 9 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_10 (hp : 10 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 10 (transLenTr ⟨18, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 10 (transLenTr ⟨18, by decide⟩ 10 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 10 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_11 (hp : 11 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 11 (transLenTr ⟨18, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 11 (transLenTr ⟨18, by decide⟩ 11 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 11 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_12 (hp : 12 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 12 (transLenTr ⟨18, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 12 (transLenTr ⟨18, by decide⟩ 12 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 12 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_13 (hp : 13 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 13 (transLenTr ⟨18, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 13 (transLenTr ⟨18, by decide⟩ 13 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 13 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_14 (hp : 14 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 14 (transLenTr ⟨18, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 14 (transLenTr ⟨18, by decide⟩ 14 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 14 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_15 (hp : 15 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 15 (transLenTr ⟨18, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 15 (transLenTr ⟨18, by decide⟩ 15 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 15 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_16 (hp : 16 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 16 (transLenTr ⟨18, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 16 (transLenTr ⟨18, by decide⟩ 16 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 16 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_17 (hp : 17 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 17 (transLenTr ⟨18, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 17 (transLenTr ⟨18, by decide⟩ 17 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 17 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_18 (hp : 18 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 18 (transLenTr ⟨18, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 18 (transLenTr ⟨18, by decide⟩ 18 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 18 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_19 (hp : 19 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 19 (transLenTr ⟨18, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 19 (transLenTr ⟨18, by decide⟩ 19 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 19 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_20 (hp : 20 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 20 (transLenTr ⟨18, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 20 (transLenTr ⟨18, by decide⟩ 20 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 20 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_21 (hp : 21 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 21 (transLenTr ⟨18, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 21 (transLenTr ⟨18, by decide⟩ 21 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 21 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_22 (hp : 22 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 22 (transLenTr ⟨18, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 22 (transLenTr ⟨18, by decide⟩ 22 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 22 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_23 (hp : 23 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 23 (transLenTr ⟨18, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 23 (transLenTr ⟨18, by decide⟩ 23 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 23 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_18_24 (hp : 24 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 24 (transLenTr ⟨18, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 24 (transLenTr ⟨18, by decide⟩ 24 hp)) T147_18
      hfix147_18 hinj147_18 hcardT147_18
      (fun i => conj_mem_of_fixedPoints _ _ (T147_18 i) (hfix147_18 i) _)
      ⟨147, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 24 hp) Q2.T147_18_2 Q2.hfix147_18_2 Q2.hinj147_18_2
      Q2.hcardT147_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_18_2 i) (Q2.hfix147_18_2 i) _)
      colCert_147_18_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T147_19
      hfix147_19 hinj147_19 hcardT147_19
      (fun i => conj_mem_of_fixedPoints _ _ (T147_19 i) (hfix147_19 i) _)
      ⟨147, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T147_19_2 Q2.hfix147_19_2 Q2.hinj147_19_2
      Q2.hcardT147_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_19_2 i) (Q2.hfix147_19_2 i) _)
      colCert_147_19_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T147_19
      hfix147_19 hinj147_19 hcardT147_19
      (fun i => conj_mem_of_fixedPoints _ _ (T147_19 i) (hfix147_19 i) _)
      ⟨147, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T147_19_2 Q2.hfix147_19_2 Q2.hinj147_19_2
      Q2.hcardT147_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_19_2 i) (Q2.hfix147_19_2 i) _)
      colCert_147_19_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T147_19
      hfix147_19 hinj147_19 hcardT147_19
      (fun i => conj_mem_of_fixedPoints _ _ (T147_19 i) (hfix147_19 i) _)
      ⟨147, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T147_19_2 Q2.hfix147_19_2 Q2.hinj147_19_2
      Q2.hcardT147_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_19_2 i) (Q2.hfix147_19_2 i) _)
      colCert_147_19_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T147_19
      hfix147_19 hinj147_19 hcardT147_19
      (fun i => conj_mem_of_fixedPoints _ _ (T147_19 i) (hfix147_19 i) _)
      ⟨147, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T147_19_2 Q2.hfix147_19_2 Q2.hinj147_19_2
      Q2.hcardT147_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_19_2 i) (Q2.hfix147_19_2 i) _)
      colCert_147_19_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T147_19
      hfix147_19 hinj147_19 hcardT147_19
      (fun i => conj_mem_of_fixedPoints _ _ (T147_19 i) (hfix147_19 i) _)
      ⟨147, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T147_19_2 Q2.hfix147_19_2 Q2.hinj147_19_2
      Q2.hcardT147_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_19_2 i) (Q2.hfix147_19_2 i) _)
      colCert_147_19_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T147_19
      hfix147_19 hinj147_19 hcardT147_19
      (fun i => conj_mem_of_fixedPoints _ _ (T147_19 i) (hfix147_19 i) _)
      ⟨147, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T147_19_2 Q2.hfix147_19_2 Q2.hinj147_19_2
      Q2.hcardT147_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_19_2 i) (Q2.hfix147_19_2 i) _)
      colCert_147_19_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T147_19
      hfix147_19 hinj147_19 hcardT147_19
      (fun i => conj_mem_of_fixedPoints _ _ (T147_19 i) (hfix147_19 i) _)
      ⟨147, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T147_19_2 Q2.hfix147_19_2 Q2.hinj147_19_2
      Q2.hcardT147_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_19_2 i) (Q2.hfix147_19_2 i) _)
      colCert_147_19_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T147_19
      hfix147_19 hinj147_19 hcardT147_19
      (fun i => conj_mem_of_fixedPoints _ _ (T147_19 i) (hfix147_19 i) _)
      ⟨147, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T147_19_2 Q2.hfix147_19_2 Q2.hinj147_19_2
      Q2.hcardT147_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_19_2 i) (Q2.hfix147_19_2 i) _)
      colCert_147_19_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T147_19
      hfix147_19 hinj147_19 hcardT147_19
      (fun i => conj_mem_of_fixedPoints _ _ (T147_19 i) (hfix147_19 i) _)
      ⟨147, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T147_19_2 Q2.hfix147_19_2 Q2.hinj147_19_2
      Q2.hcardT147_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_19_2 i) (Q2.hfix147_19_2 i) _)
      colCert_147_19_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T147_20
      hfix147_20 hinj147_20 hcardT147_20
      (fun i => conj_mem_of_fixedPoints _ _ (T147_20 i) (hfix147_20 i) _)
      ⟨147, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T147_20_2 Q2.hfix147_20_2 Q2.hinj147_20_2
      Q2.hcardT147_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_20_2 i) (Q2.hfix147_20_2 i) _)
      colCert_147_20_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T147_20
      hfix147_20 hinj147_20 hcardT147_20
      (fun i => conj_mem_of_fixedPoints _ _ (T147_20 i) (hfix147_20 i) _)
      ⟨147, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T147_20_2 Q2.hfix147_20_2 Q2.hinj147_20_2
      Q2.hcardT147_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_20_2 i) (Q2.hfix147_20_2 i) _)
      colCert_147_20_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T147_20
      hfix147_20 hinj147_20 hcardT147_20
      (fun i => conj_mem_of_fixedPoints _ _ (T147_20 i) (hfix147_20 i) _)
      ⟨147, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T147_20_2 Q2.hfix147_20_2 Q2.hinj147_20_2
      Q2.hcardT147_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_20_2 i) (Q2.hfix147_20_2 i) _)
      colCert_147_20_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T147_20
      hfix147_20 hinj147_20 hcardT147_20
      (fun i => conj_mem_of_fixedPoints _ _ (T147_20 i) (hfix147_20 i) _)
      ⟨147, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T147_20_2 Q2.hfix147_20_2 Q2.hinj147_20_2
      Q2.hcardT147_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_20_2 i) (Q2.hfix147_20_2 i) _)
      colCert_147_20_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T147_20
      hfix147_20 hinj147_20 hcardT147_20
      (fun i => conj_mem_of_fixedPoints _ _ (T147_20 i) (hfix147_20 i) _)
      ⟨147, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T147_20_2 Q2.hfix147_20_2 Q2.hinj147_20_2
      Q2.hcardT147_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_20_2 i) (Q2.hfix147_20_2 i) _)
      colCert_147_20_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T147_20
      hfix147_20 hinj147_20 hcardT147_20
      (fun i => conj_mem_of_fixedPoints _ _ (T147_20 i) (hfix147_20 i) _)
      ⟨147, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T147_20_2 Q2.hfix147_20_2 Q2.hinj147_20_2
      Q2.hcardT147_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_20_2 i) (Q2.hfix147_20_2 i) _)
      colCert_147_20_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T147_20
      hfix147_20 hinj147_20 hcardT147_20
      (fun i => conj_mem_of_fixedPoints _ _ (T147_20 i) (hfix147_20 i) _)
      ⟨147, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T147_20_2 Q2.hfix147_20_2 Q2.hinj147_20_2
      Q2.hcardT147_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_20_2 i) (Q2.hfix147_20_2 i) _)
      colCert_147_20_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T147_20
      hfix147_20 hinj147_20 hcardT147_20
      (fun i => conj_mem_of_fixedPoints _ _ (T147_20 i) (hfix147_20 i) _)
      ⟨147, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T147_20_2 Q2.hfix147_20_2 Q2.hinj147_20_2
      Q2.hcardT147_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_20_2 i) (Q2.hfix147_20_2 i) _)
      colCert_147_20_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T147_20
      hfix147_20 hinj147_20 hcardT147_20
      (fun i => conj_mem_of_fixedPoints _ _ (T147_20 i) (hfix147_20 i) _)
      ⟨147, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T147_20_2 Q2.hfix147_20_2 Q2.hinj147_20_2
      Q2.hcardT147_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_20_2 i) (Q2.hfix147_20_2 i) _)
      colCert_147_20_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T147_21
      hfix147_21 hinj147_21 hcardT147_21
      (fun i => conj_mem_of_fixedPoints _ _ (T147_21 i) (hfix147_21 i) _)
      ⟨147, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T147_21_2 Q2.hfix147_21_2 Q2.hinj147_21_2
      Q2.hcardT147_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_21_2 i) (Q2.hfix147_21_2 i) _)
      colCert_147_21_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T147_21
      hfix147_21 hinj147_21 hcardT147_21
      (fun i => conj_mem_of_fixedPoints _ _ (T147_21 i) (hfix147_21 i) _)
      ⟨147, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T147_21_2 Q2.hfix147_21_2 Q2.hinj147_21_2
      Q2.hcardT147_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_21_2 i) (Q2.hfix147_21_2 i) _)
      colCert_147_21_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T147_21
      hfix147_21 hinj147_21 hcardT147_21
      (fun i => conj_mem_of_fixedPoints _ _ (T147_21 i) (hfix147_21 i) _)
      ⟨147, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T147_21_2 Q2.hfix147_21_2 Q2.hinj147_21_2
      Q2.hcardT147_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_21_2 i) (Q2.hfix147_21_2 i) _)
      colCert_147_21_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T147_21
      hfix147_21 hinj147_21 hcardT147_21
      (fun i => conj_mem_of_fixedPoints _ _ (T147_21 i) (hfix147_21 i) _)
      ⟨147, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T147_21_2 Q2.hfix147_21_2 Q2.hinj147_21_2
      Q2.hcardT147_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_21_2 i) (Q2.hfix147_21_2 i) _)
      colCert_147_21_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T147_21
      hfix147_21 hinj147_21 hcardT147_21
      (fun i => conj_mem_of_fixedPoints _ _ (T147_21 i) (hfix147_21 i) _)
      ⟨147, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T147_21_2 Q2.hfix147_21_2 Q2.hinj147_21_2
      Q2.hcardT147_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_21_2 i) (Q2.hfix147_21_2 i) _)
      colCert_147_21_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T147_21
      hfix147_21 hinj147_21 hcardT147_21
      (fun i => conj_mem_of_fixedPoints _ _ (T147_21 i) (hfix147_21 i) _)
      ⟨147, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T147_21_2 Q2.hfix147_21_2 Q2.hinj147_21_2
      Q2.hcardT147_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_21_2 i) (Q2.hfix147_21_2 i) _)
      colCert_147_21_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T147_21
      hfix147_21 hinj147_21 hcardT147_21
      (fun i => conj_mem_of_fixedPoints _ _ (T147_21 i) (hfix147_21 i) _)
      ⟨147, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T147_21_2 Q2.hfix147_21_2 Q2.hinj147_21_2
      Q2.hcardT147_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_21_2 i) (Q2.hfix147_21_2 i) _)
      colCert_147_21_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T147_21
      hfix147_21 hinj147_21 hcardT147_21
      (fun i => conj_mem_of_fixedPoints _ _ (T147_21 i) (hfix147_21 i) _)
      ⟨147, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T147_21_2 Q2.hfix147_21_2 Q2.hinj147_21_2
      Q2.hcardT147_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_21_2 i) (Q2.hfix147_21_2 i) _)
      colCert_147_21_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T147_21
      hfix147_21 hinj147_21 hcardT147_21
      (fun i => conj_mem_of_fixedPoints _ _ (T147_21 i) (hfix147_21 i) _)
      ⟨147, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T147_21_2 Q2.hfix147_21_2 Q2.hinj147_21_2
      Q2.hcardT147_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_21_2 i) (Q2.hfix147_21_2 i) _)
      colCert_147_21_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T147_22
      hfix147_22 hinj147_22 hcardT147_22
      (fun i => conj_mem_of_fixedPoints _ _ (T147_22 i) (hfix147_22 i) _)
      ⟨147, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T147_22_2 Q2.hfix147_22_2 Q2.hinj147_22_2
      Q2.hcardT147_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_22_2 i) (Q2.hfix147_22_2 i) _)
      colCert_147_22_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T147_22
      hfix147_22 hinj147_22 hcardT147_22
      (fun i => conj_mem_of_fixedPoints _ _ (T147_22 i) (hfix147_22 i) _)
      ⟨147, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T147_22_2 Q2.hfix147_22_2 Q2.hinj147_22_2
      Q2.hcardT147_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_22_2 i) (Q2.hfix147_22_2 i) _)
      colCert_147_22_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T147_22
      hfix147_22 hinj147_22 hcardT147_22
      (fun i => conj_mem_of_fixedPoints _ _ (T147_22 i) (hfix147_22 i) _)
      ⟨147, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T147_22_2 Q2.hfix147_22_2 Q2.hinj147_22_2
      Q2.hcardT147_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_22_2 i) (Q2.hfix147_22_2 i) _)
      colCert_147_22_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T147_22
      hfix147_22 hinj147_22 hcardT147_22
      (fun i => conj_mem_of_fixedPoints _ _ (T147_22 i) (hfix147_22 i) _)
      ⟨147, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T147_22_2 Q2.hfix147_22_2 Q2.hinj147_22_2
      Q2.hcardT147_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_22_2 i) (Q2.hfix147_22_2 i) _)
      colCert_147_22_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T147_22
      hfix147_22 hinj147_22 hcardT147_22
      (fun i => conj_mem_of_fixedPoints _ _ (T147_22 i) (hfix147_22 i) _)
      ⟨147, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T147_22_2 Q2.hfix147_22_2 Q2.hinj147_22_2
      Q2.hcardT147_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_22_2 i) (Q2.hfix147_22_2 i) _)
      colCert_147_22_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T147_22
      hfix147_22 hinj147_22 hcardT147_22
      (fun i => conj_mem_of_fixedPoints _ _ (T147_22 i) (hfix147_22 i) _)
      ⟨147, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T147_22_2 Q2.hfix147_22_2 Q2.hinj147_22_2
      Q2.hcardT147_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_22_2 i) (Q2.hfix147_22_2 i) _)
      colCert_147_22_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T147_22
      hfix147_22 hinj147_22 hcardT147_22
      (fun i => conj_mem_of_fixedPoints _ _ (T147_22 i) (hfix147_22 i) _)
      ⟨147, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T147_22_2 Q2.hfix147_22_2 Q2.hinj147_22_2
      Q2.hcardT147_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_22_2 i) (Q2.hfix147_22_2 i) _)
      colCert_147_22_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T147_22
      hfix147_22 hinj147_22 hcardT147_22
      (fun i => conj_mem_of_fixedPoints _ _ (T147_22 i) (hfix147_22 i) _)
      ⟨147, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T147_22_2 Q2.hfix147_22_2 Q2.hinj147_22_2
      Q2.hcardT147_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_22_2 i) (Q2.hfix147_22_2 i) _)
      colCert_147_22_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T147_22
      hfix147_22 hinj147_22 hcardT147_22
      (fun i => conj_mem_of_fixedPoints _ _ (T147_22 i) (hfix147_22 i) _)
      ⟨147, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T147_22_2 Q2.hfix147_22_2 Q2.hinj147_22_2
      Q2.hcardT147_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_22_2 i) (Q2.hfix147_22_2 i) _)
      colCert_147_22_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T147_23
      hfix147_23 hinj147_23 hcardT147_23
      (fun i => conj_mem_of_fixedPoints _ _ (T147_23 i) (hfix147_23 i) _)
      ⟨147, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T147_23_2 Q2.hfix147_23_2 Q2.hinj147_23_2
      Q2.hcardT147_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_23_2 i) (Q2.hfix147_23_2 i) _)
      colCert_147_23_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T147_23
      hfix147_23 hinj147_23 hcardT147_23
      (fun i => conj_mem_of_fixedPoints _ _ (T147_23 i) (hfix147_23 i) _)
      ⟨147, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T147_23_2 Q2.hfix147_23_2 Q2.hinj147_23_2
      Q2.hcardT147_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_23_2 i) (Q2.hfix147_23_2 i) _)
      colCert_147_23_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T147_23
      hfix147_23 hinj147_23 hcardT147_23
      (fun i => conj_mem_of_fixedPoints _ _ (T147_23 i) (hfix147_23 i) _)
      ⟨147, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T147_23_2 Q2.hfix147_23_2 Q2.hinj147_23_2
      Q2.hcardT147_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_23_2 i) (Q2.hfix147_23_2 i) _)
      colCert_147_23_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T147_23
      hfix147_23 hinj147_23 hcardT147_23
      (fun i => conj_mem_of_fixedPoints _ _ (T147_23 i) (hfix147_23 i) _)
      ⟨147, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T147_23_2 Q2.hfix147_23_2 Q2.hinj147_23_2
      Q2.hcardT147_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_23_2 i) (Q2.hfix147_23_2 i) _)
      colCert_147_23_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T147_23
      hfix147_23 hinj147_23 hcardT147_23
      (fun i => conj_mem_of_fixedPoints _ _ (T147_23 i) (hfix147_23 i) _)
      ⟨147, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T147_23_2 Q2.hfix147_23_2 Q2.hinj147_23_2
      Q2.hcardT147_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_23_2 i) (Q2.hfix147_23_2 i) _)
      colCert_147_23_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T147_23
      hfix147_23 hinj147_23 hcardT147_23
      (fun i => conj_mem_of_fixedPoints _ _ (T147_23 i) (hfix147_23 i) _)
      ⟨147, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T147_23_2 Q2.hfix147_23_2 Q2.hinj147_23_2
      Q2.hcardT147_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_23_2 i) (Q2.hfix147_23_2 i) _)
      colCert_147_23_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T147_23
      hfix147_23 hinj147_23 hcardT147_23
      (fun i => conj_mem_of_fixedPoints _ _ (T147_23 i) (hfix147_23 i) _)
      ⟨147, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T147_23_2 Q2.hfix147_23_2 Q2.hinj147_23_2
      Q2.hcardT147_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_23_2 i) (Q2.hfix147_23_2 i) _)
      colCert_147_23_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T147_23
      hfix147_23 hinj147_23 hcardT147_23
      (fun i => conj_mem_of_fixedPoints _ _ (T147_23 i) (hfix147_23 i) _)
      ⟨147, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T147_23_2 Q2.hfix147_23_2 Q2.hinj147_23_2
      Q2.hcardT147_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_23_2 i) (Q2.hfix147_23_2 i) _)
      colCert_147_23_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T147_23
      hfix147_23 hinj147_23 hcardT147_23
      (fun i => conj_mem_of_fixedPoints _ _ (T147_23 i) (hfix147_23 i) _)
      ⟨147, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T147_23_2 Q2.hfix147_23_2 Q2.hinj147_23_2
      Q2.hcardT147_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_23_2 i) (Q2.hfix147_23_2 i) _)
      colCert_147_23_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T147_24
      hfix147_24 hinj147_24 hcardT147_24
      (fun i => conj_mem_of_fixedPoints _ _ (T147_24 i) (hfix147_24 i) _)
      ⟨147, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T147_24_2 Q2.hfix147_24_2 Q2.hinj147_24_2
      Q2.hcardT147_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_24_2 i) (Q2.hfix147_24_2 i) _)
      colCert_147_24_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T147_24
      hfix147_24 hinj147_24 hcardT147_24
      (fun i => conj_mem_of_fixedPoints _ _ (T147_24 i) (hfix147_24 i) _)
      ⟨147, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T147_24_2 Q2.hfix147_24_2 Q2.hinj147_24_2
      Q2.hcardT147_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_24_2 i) (Q2.hfix147_24_2 i) _)
      colCert_147_24_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T147_24
      hfix147_24 hinj147_24 hcardT147_24
      (fun i => conj_mem_of_fixedPoints _ _ (T147_24 i) (hfix147_24 i) _)
      ⟨147, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T147_24_2 Q2.hfix147_24_2 Q2.hinj147_24_2
      Q2.hcardT147_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_24_2 i) (Q2.hfix147_24_2 i) _)
      colCert_147_24_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T147_24
      hfix147_24 hinj147_24 hcardT147_24
      (fun i => conj_mem_of_fixedPoints _ _ (T147_24 i) (hfix147_24 i) _)
      ⟨147, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T147_24_2 Q2.hfix147_24_2 Q2.hinj147_24_2
      Q2.hcardT147_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_24_2 i) (Q2.hfix147_24_2 i) _)
      colCert_147_24_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T147_24
      hfix147_24 hinj147_24 hcardT147_24
      (fun i => conj_mem_of_fixedPoints _ _ (T147_24 i) (hfix147_24 i) _)
      ⟨147, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T147_24_2 Q2.hfix147_24_2 Q2.hinj147_24_2
      Q2.hcardT147_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_24_2 i) (Q2.hfix147_24_2 i) _)
      colCert_147_24_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T147_24
      hfix147_24 hinj147_24 hcardT147_24
      (fun i => conj_mem_of_fixedPoints _ _ (T147_24 i) (hfix147_24 i) _)
      ⟨147, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T147_24_2 Q2.hfix147_24_2 Q2.hinj147_24_2
      Q2.hcardT147_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_24_2 i) (Q2.hfix147_24_2 i) _)
      colCert_147_24_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T147_24
      hfix147_24 hinj147_24 hcardT147_24
      (fun i => conj_mem_of_fixedPoints _ _ (T147_24 i) (hfix147_24 i) _)
      ⟨147, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T147_24_2 Q2.hfix147_24_2 Q2.hinj147_24_2
      Q2.hcardT147_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_24_2 i) (Q2.hfix147_24_2 i) _)
      colCert_147_24_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T147_24
      hfix147_24 hinj147_24 hcardT147_24
      (fun i => conj_mem_of_fixedPoints _ _ (T147_24 i) (hfix147_24 i) _)
      ⟨147, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T147_24_2 Q2.hfix147_24_2 Q2.hinj147_24_2
      Q2.hcardT147_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_24_2 i) (Q2.hfix147_24_2 i) _)
      colCert_147_24_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T147_24
      hfix147_24 hinj147_24 hcardT147_24
      (fun i => conj_mem_of_fixedPoints _ _ (T147_24 i) (hfix147_24 i) _)
      ⟨147, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T147_24_2 Q2.hfix147_24_2 Q2.hinj147_24_2
      Q2.hcardT147_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_24_2 i) (Q2.hfix147_24_2 i) _)
      colCert_147_24_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T147_25
      hfix147_25 hinj147_25 hcardT147_25
      (fun i => conj_mem_of_fixedPoints _ _ (T147_25 i) (hfix147_25 i) _)
      ⟨147, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T147_25_2 Q2.hfix147_25_2 Q2.hinj147_25_2
      Q2.hcardT147_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_25_2 i) (Q2.hfix147_25_2 i) _)
      colCert_147_25_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T147_25
      hfix147_25 hinj147_25 hcardT147_25
      (fun i => conj_mem_of_fixedPoints _ _ (T147_25 i) (hfix147_25 i) _)
      ⟨147, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T147_25_2 Q2.hfix147_25_2 Q2.hinj147_25_2
      Q2.hcardT147_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_25_2 i) (Q2.hfix147_25_2 i) _)
      colCert_147_25_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T147_25
      hfix147_25 hinj147_25 hcardT147_25
      (fun i => conj_mem_of_fixedPoints _ _ (T147_25 i) (hfix147_25 i) _)
      ⟨147, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T147_25_2 Q2.hfix147_25_2 Q2.hinj147_25_2
      Q2.hcardT147_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_25_2 i) (Q2.hfix147_25_2 i) _)
      colCert_147_25_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T147_25
      hfix147_25 hinj147_25 hcardT147_25
      (fun i => conj_mem_of_fixedPoints _ _ (T147_25 i) (hfix147_25 i) _)
      ⟨147, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T147_25_2 Q2.hfix147_25_2 Q2.hinj147_25_2
      Q2.hcardT147_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_25_2 i) (Q2.hfix147_25_2 i) _)
      colCert_147_25_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T147_25
      hfix147_25 hinj147_25 hcardT147_25
      (fun i => conj_mem_of_fixedPoints _ _ (T147_25 i) (hfix147_25 i) _)
      ⟨147, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T147_25_2 Q2.hfix147_25_2 Q2.hinj147_25_2
      Q2.hcardT147_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_25_2 i) (Q2.hfix147_25_2 i) _)
      colCert_147_25_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T147_25
      hfix147_25 hinj147_25 hcardT147_25
      (fun i => conj_mem_of_fixedPoints _ _ (T147_25 i) (hfix147_25 i) _)
      ⟨147, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T147_25_2 Q2.hfix147_25_2 Q2.hinj147_25_2
      Q2.hcardT147_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_25_2 i) (Q2.hfix147_25_2 i) _)
      colCert_147_25_5.hD ?_).symm
  rw [alnId_147 j hj]


end LeanDring.P5Presentation
