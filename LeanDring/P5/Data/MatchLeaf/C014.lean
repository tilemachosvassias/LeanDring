/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColRestCheap.C174
import LeanDring.P5.Data.ColRestCheap.C175
import LeanDring.P5.Data.ColRestCheap.C176
import LeanDring.P5.Data.ColRestCheap.C177
import LeanDring.P5.Data.ColRestCheap.C178
import LeanDring.P5.Data.ColTau.C004
import LeanDring.P5.Data.EntryK.C018
import LeanDring.P5.Data.EntryK.C019
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk01

/-! # Stage-5 leaves, chunk 13 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_79_79_21 (hp : 21 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 21 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 21 (transLenTr ⟨79, by decide⟩ 21 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 21 (transLenTr ⟨79, by decide⟩ 21 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 21 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_21.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_22 (hp : 22 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 22 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 22 (transLenTr ⟨79, by decide⟩ 22 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 22 (transLenTr ⟨79, by decide⟩ 22 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 22 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_22.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_23 (hp : 23 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 23 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 23 (transLenTr ⟨79, by decide⟩ 23 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 23 (transLenTr ⟨79, by decide⟩ 23 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 23 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_23.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_79_79_24 (hp : 24 < (Q2.transData.getD 79 []).length)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨79, by decide⟩ : Fin 148)) (colE2 ⟨79, by decide⟩ 24 hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨79, by decide⟩ : Fin 148))
        (colE1 ⟨79, by decide⟩ 24 (transLenTr ⟨79, by decide⟩ 24 hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨79, by decide⟩ : Fin 148) ⟨79, by decide⟩ _
      (validAt ⟨79, by decide⟩ (listedAt ⟨79, by decide⟩ hj))
      (colE1 ⟨79, by decide⟩ 24 (transLenTr ⟨79, by decide⟩ 24 hp)) T79_79
      hfix79_79 hinj79_79 hcardT79_79
      (fun i => conj_mem_of_fixedPoints _ _ (T79_79 i) (hfix79_79 i) _)
      ⟨79, by decide⟩ ⟨79, by decide⟩ _
      (Q2.validAt ⟨79, by decide⟩ (Q2.listedAt ⟨79, by decide⟩
        (alnCheck_rep ⟨79, by decide⟩ hj hq).1))
      (colE2 ⟨79, by decide⟩ 24 hp) Q2.T79_79_2 Q2.hfix79_79_2 Q2.hinj79_79_2
      Q2.hcardT79_79_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T79_79_2 i) (Q2.hfix79_79_2 i) _)
      colCert_79_79_24.hD ?_).symm
  rw [alnId_79 j hj]


theorem leaf_80_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T80_1
      hfix80_1 hinj80_1 hcardT80_1
      (fun i => conj_mem_of_fixedPoints _ _ (T80_1 i) (hfix80_1 i) _)
      ⟨80, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T80_1_2 Q2.hfix80_1_2 Q2.hinj80_1_2
      Q2.hcardT80_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_1_2 i) (Q2.hfix80_1_2 i) _)
      colCert_80_1_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T80_1
      hfix80_1 hinj80_1 hcardT80_1
      (fun i => conj_mem_of_fixedPoints _ _ (T80_1 i) (hfix80_1 i) _)
      ⟨80, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T80_1_2 Q2.hfix80_1_2 Q2.hinj80_1_2
      Q2.hcardT80_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_1_2 i) (Q2.hfix80_1_2 i) _)
      colCert_80_1_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T80_1
      hfix80_1 hinj80_1 hcardT80_1
      (fun i => conj_mem_of_fixedPoints _ _ (T80_1 i) (hfix80_1 i) _)
      ⟨80, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T80_1_2 Q2.hfix80_1_2 Q2.hinj80_1_2
      Q2.hcardT80_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_1_2 i) (Q2.hfix80_1_2 i) _)
      colCert_80_1_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T80_1
      hfix80_1 hinj80_1 hcardT80_1
      (fun i => conj_mem_of_fixedPoints _ _ (T80_1 i) (hfix80_1 i) _)
      ⟨80, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T80_1_2 Q2.hfix80_1_2 Q2.hinj80_1_2
      Q2.hcardT80_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_1_2 i) (Q2.hfix80_1_2 i) _)
      colCert_80_1_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T80_1
      hfix80_1 hinj80_1 hcardT80_1
      (fun i => conj_mem_of_fixedPoints _ _ (T80_1 i) (hfix80_1 i) _)
      ⟨80, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T80_1_2 Q2.hfix80_1_2 Q2.hinj80_1_2
      Q2.hcardT80_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_1_2 i) (Q2.hfix80_1_2 i) _)
      colCert_80_1_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T80_6
      hfix80_6 hinj80_6 hcardT80_6
      (fun i => conj_mem_of_fixedPoints _ _ (T80_6 i) (hfix80_6 i) _)
      ⟨80, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T80_6_2 Q2.hfix80_6_2 Q2.hinj80_6_2
      Q2.hcardT80_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_6_2 i) (Q2.hfix80_6_2 i) _)
      colCert_80_6_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T80_6
      hfix80_6 hinj80_6 hcardT80_6
      (fun i => conj_mem_of_fixedPoints _ _ (T80_6 i) (hfix80_6 i) _)
      ⟨80, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T80_6_2 Q2.hfix80_6_2 Q2.hinj80_6_2
      Q2.hcardT80_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_6_2 i) (Q2.hfix80_6_2 i) _)
      colCert_80_6_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T80_6
      hfix80_6 hinj80_6 hcardT80_6
      (fun i => conj_mem_of_fixedPoints _ _ (T80_6 i) (hfix80_6 i) _)
      ⟨80, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T80_6_2 Q2.hfix80_6_2 Q2.hinj80_6_2
      Q2.hcardT80_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_6_2 i) (Q2.hfix80_6_2 i) _)
      colCert_80_6_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T80_6
      hfix80_6 hinj80_6 hcardT80_6
      (fun i => conj_mem_of_fixedPoints _ _ (T80_6 i) (hfix80_6 i) _)
      ⟨80, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T80_6_2 Q2.hfix80_6_2 Q2.hinj80_6_2
      Q2.hcardT80_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_6_2 i) (Q2.hfix80_6_2 i) _)
      colCert_80_6_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T80_6
      hfix80_6 hinj80_6 hcardT80_6
      (fun i => conj_mem_of_fixedPoints _ _ (T80_6 i) (hfix80_6 i) _)
      ⟨80, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T80_6_2 Q2.hfix80_6_2 Q2.hinj80_6_2
      Q2.hcardT80_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_6_2 i) (Q2.hfix80_6_2 i) _)
      colCert_80_6_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T80_7
      hfix80_7 hinj80_7 hcardT80_7
      (fun i => conj_mem_of_fixedPoints _ _ (T80_7 i) (hfix80_7 i) _)
      ⟨80, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T80_7_2 Q2.hfix80_7_2 Q2.hinj80_7_2
      Q2.hcardT80_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_7_2 i) (Q2.hfix80_7_2 i) _)
      colCert_80_7_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T80_7
      hfix80_7 hinj80_7 hcardT80_7
      (fun i => conj_mem_of_fixedPoints _ _ (T80_7 i) (hfix80_7 i) _)
      ⟨80, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T80_7_2 Q2.hfix80_7_2 Q2.hinj80_7_2
      Q2.hcardT80_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_7_2 i) (Q2.hfix80_7_2 i) _)
      colCert_80_7_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T80_7
      hfix80_7 hinj80_7 hcardT80_7
      (fun i => conj_mem_of_fixedPoints _ _ (T80_7 i) (hfix80_7 i) _)
      ⟨80, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T80_7_2 Q2.hfix80_7_2 Q2.hinj80_7_2
      Q2.hcardT80_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_7_2 i) (Q2.hfix80_7_2 i) _)
      colCert_80_7_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T80_7
      hfix80_7 hinj80_7 hcardT80_7
      (fun i => conj_mem_of_fixedPoints _ _ (T80_7 i) (hfix80_7 i) _)
      ⟨80, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T80_7_2 Q2.hfix80_7_2 Q2.hinj80_7_2
      Q2.hcardT80_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_7_2 i) (Q2.hfix80_7_2 i) _)
      colCert_80_7_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T80_7
      hfix80_7 hinj80_7 hcardT80_7
      (fun i => conj_mem_of_fixedPoints _ _ (T80_7 i) (hfix80_7 i) _)
      ⟨80, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T80_7_2 Q2.hfix80_7_2 Q2.hinj80_7_2
      Q2.hcardT80_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_7_2 i) (Q2.hfix80_7_2 i) _)
      colCert_80_7_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T80_8
      hfix80_8 hinj80_8 hcardT80_8
      (fun i => conj_mem_of_fixedPoints _ _ (T80_8 i) (hfix80_8 i) _)
      ⟨80, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T80_8_2 Q2.hfix80_8_2 Q2.hinj80_8_2
      Q2.hcardT80_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_8_2 i) (Q2.hfix80_8_2 i) _)
      colCert_80_8_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T80_8
      hfix80_8 hinj80_8 hcardT80_8
      (fun i => conj_mem_of_fixedPoints _ _ (T80_8 i) (hfix80_8 i) _)
      ⟨80, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T80_8_2 Q2.hfix80_8_2 Q2.hinj80_8_2
      Q2.hcardT80_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_8_2 i) (Q2.hfix80_8_2 i) _)
      colCert_80_8_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T80_8
      hfix80_8 hinj80_8 hcardT80_8
      (fun i => conj_mem_of_fixedPoints _ _ (T80_8 i) (hfix80_8 i) _)
      ⟨80, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T80_8_2 Q2.hfix80_8_2 Q2.hinj80_8_2
      Q2.hcardT80_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_8_2 i) (Q2.hfix80_8_2 i) _)
      colCert_80_8_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T80_8
      hfix80_8 hinj80_8 hcardT80_8
      (fun i => conj_mem_of_fixedPoints _ _ (T80_8 i) (hfix80_8 i) _)
      ⟨80, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T80_8_2 Q2.hfix80_8_2 Q2.hinj80_8_2
      Q2.hcardT80_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_8_2 i) (Q2.hfix80_8_2 i) _)
      colCert_80_8_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T80_8
      hfix80_8 hinj80_8 hcardT80_8
      (fun i => conj_mem_of_fixedPoints _ _ (T80_8 i) (hfix80_8 i) _)
      ⟨80, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T80_8_2 Q2.hfix80_8_2 Q2.hinj80_8_2
      Q2.hcardT80_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_8_2 i) (Q2.hfix80_8_2 i) _)
      colCert_80_8_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T80_9
      hfix80_9 hinj80_9 hcardT80_9
      (fun i => conj_mem_of_fixedPoints _ _ (T80_9 i) (hfix80_9 i) _)
      ⟨80, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T80_9_2 Q2.hfix80_9_2 Q2.hinj80_9_2
      Q2.hcardT80_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_9_2 i) (Q2.hfix80_9_2 i) _)
      colCert_80_9_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T80_9
      hfix80_9 hinj80_9 hcardT80_9
      (fun i => conj_mem_of_fixedPoints _ _ (T80_9 i) (hfix80_9 i) _)
      ⟨80, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T80_9_2 Q2.hfix80_9_2 Q2.hinj80_9_2
      Q2.hcardT80_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_9_2 i) (Q2.hfix80_9_2 i) _)
      colCert_80_9_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T80_9
      hfix80_9 hinj80_9 hcardT80_9
      (fun i => conj_mem_of_fixedPoints _ _ (T80_9 i) (hfix80_9 i) _)
      ⟨80, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T80_9_2 Q2.hfix80_9_2 Q2.hinj80_9_2
      Q2.hcardT80_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_9_2 i) (Q2.hfix80_9_2 i) _)
      colCert_80_9_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T80_9
      hfix80_9 hinj80_9 hcardT80_9
      (fun i => conj_mem_of_fixedPoints _ _ (T80_9 i) (hfix80_9 i) _)
      ⟨80, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T80_9_2 Q2.hfix80_9_2 Q2.hinj80_9_2
      Q2.hcardT80_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_9_2 i) (Q2.hfix80_9_2 i) _)
      colCert_80_9_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T80_9
      hfix80_9 hinj80_9 hcardT80_9
      (fun i => conj_mem_of_fixedPoints _ _ (T80_9 i) (hfix80_9 i) _)
      ⟨80, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T80_9_2 Q2.hfix80_9_2 Q2.hinj80_9_2
      Q2.hcardT80_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_9_2 i) (Q2.hfix80_9_2 i) _)
      colCert_80_9_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T80_10
      hfix80_10 hinj80_10 hcardT80_10
      (fun i => conj_mem_of_fixedPoints _ _ (T80_10 i) (hfix80_10 i) _)
      ⟨80, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T80_10_2 Q2.hfix80_10_2 Q2.hinj80_10_2
      Q2.hcardT80_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_10_2 i) (Q2.hfix80_10_2 i) _)
      colCert_80_10_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T80_10
      hfix80_10 hinj80_10 hcardT80_10
      (fun i => conj_mem_of_fixedPoints _ _ (T80_10 i) (hfix80_10 i) _)
      ⟨80, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T80_10_2 Q2.hfix80_10_2 Q2.hinj80_10_2
      Q2.hcardT80_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_10_2 i) (Q2.hfix80_10_2 i) _)
      colCert_80_10_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T80_10
      hfix80_10 hinj80_10 hcardT80_10
      (fun i => conj_mem_of_fixedPoints _ _ (T80_10 i) (hfix80_10 i) _)
      ⟨80, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T80_10_2 Q2.hfix80_10_2 Q2.hinj80_10_2
      Q2.hcardT80_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_10_2 i) (Q2.hfix80_10_2 i) _)
      colCert_80_10_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T80_10
      hfix80_10 hinj80_10 hcardT80_10
      (fun i => conj_mem_of_fixedPoints _ _ (T80_10 i) (hfix80_10 i) _)
      ⟨80, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T80_10_2 Q2.hfix80_10_2 Q2.hinj80_10_2
      Q2.hcardT80_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_10_2 i) (Q2.hfix80_10_2 i) _)
      colCert_80_10_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T80_10
      hfix80_10 hinj80_10 hcardT80_10
      (fun i => conj_mem_of_fixedPoints _ _ (T80_10 i) (hfix80_10 i) _)
      ⟨80, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T80_10_2 Q2.hfix80_10_2 Q2.hinj80_10_2
      Q2.hcardT80_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_10_2 i) (Q2.hfix80_10_2 i) _)
      colCert_80_10_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T80_12
      hfix80_12 hinj80_12 hcardT80_12
      (fun i => conj_mem_of_fixedPoints _ _ (T80_12 i) (hfix80_12 i) _)
      ⟨80, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T80_12_2 Q2.hfix80_12_2 Q2.hinj80_12_2
      Q2.hcardT80_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_12_2 i) (Q2.hfix80_12_2 i) _)
      colCert_80_12_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T80_12
      hfix80_12 hinj80_12 hcardT80_12
      (fun i => conj_mem_of_fixedPoints _ _ (T80_12 i) (hfix80_12 i) _)
      ⟨80, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T80_12_2 Q2.hfix80_12_2 Q2.hinj80_12_2
      Q2.hcardT80_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_12_2 i) (Q2.hfix80_12_2 i) _)
      colCert_80_12_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T80_12
      hfix80_12 hinj80_12 hcardT80_12
      (fun i => conj_mem_of_fixedPoints _ _ (T80_12 i) (hfix80_12 i) _)
      ⟨80, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T80_12_2 Q2.hfix80_12_2 Q2.hinj80_12_2
      Q2.hcardT80_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_12_2 i) (Q2.hfix80_12_2 i) _)
      colCert_80_12_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T80_12
      hfix80_12 hinj80_12 hcardT80_12
      (fun i => conj_mem_of_fixedPoints _ _ (T80_12 i) (hfix80_12 i) _)
      ⟨80, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T80_12_2 Q2.hfix80_12_2 Q2.hinj80_12_2
      Q2.hcardT80_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_12_2 i) (Q2.hfix80_12_2 i) _)
      colCert_80_12_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T80_12
      hfix80_12 hinj80_12 hcardT80_12
      (fun i => conj_mem_of_fixedPoints _ _ (T80_12 i) (hfix80_12 i) _)
      ⟨80, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T80_12_2 Q2.hfix80_12_2 Q2.hinj80_12_2
      Q2.hcardT80_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_12_2 i) (Q2.hfix80_12_2 i) _)
      colCert_80_12_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_0 (hp : 0 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 0 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_1 (hp : 1 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 1 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_2 (hp : 2 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 2 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_3 (hp : 3 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 3 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_4 (hp : 4 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 4 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_5 (hp : 5 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 5 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 5 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨80, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T80_13 = colFn colCertDiv_80_13_5.D1 (m := 25) from colCertDiv_80_13_5.bind1,
    show colData2 (⟨80, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 5 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T80_13_2 = colFn colCertDiv_80_13_5.D2 (m := 25) from colCertDiv_80_13_5.bind2]
  rw [alnId_80 j hj]
  exact fastcode_of_tau ⟨80, by decide⟩ _ _ _
    ((alnId_80 j hj) ▸ Q2.listedAt (⟨80, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨80, by decide⟩ : Fin 148) hj hq).1) colCertDiv_80_13_5_tau_match


theorem leaf_80_13_6 (hp : 6 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 6 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 6 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨80, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T80_13 = colFn colCertDiv_80_13_6.D1 (m := 25) from colCertDiv_80_13_6.bind1,
    show colData2 (⟨80, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 6 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T80_13_2 = colFn colCertDiv_80_13_6.D2 (m := 25) from colCertDiv_80_13_6.bind2]
  rw [alnId_80 j hj]
  exact fastcode_of_tau ⟨80, by decide⟩ _ _ _
    ((alnId_80 j hj) ▸ Q2.listedAt (⟨80, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨80, by decide⟩ : Fin 148) hj hq).1) colCertDiv_80_13_6_tau_match


theorem leaf_80_13_7 (hp : 7 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 7 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 7 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨80, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T80_13 = colFn colCertDiv_80_13_7.D1 (m := 25) from colCertDiv_80_13_7.bind1,
    show colData2 (⟨80, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 7 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T80_13_2 = colFn colCertDiv_80_13_7.D2 (m := 25) from colCertDiv_80_13_7.bind2]
  rw [alnId_80 j hj]
  exact fastcode_of_tau ⟨80, by decide⟩ _ _ _
    ((alnId_80 j hj) ▸ Q2.listedAt (⟨80, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨80, by decide⟩ : Fin 148) hj hq).1) colCertDiv_80_13_7_tau_match


theorem leaf_80_13_8 (hp : 8 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 8 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 8 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨80, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T80_13 = colFn colCertDiv_80_13_8.D1 (m := 25) from colCertDiv_80_13_8.bind1,
    show colData2 (⟨80, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 8 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T80_13_2 = colFn colCertDiv_80_13_8.D2 (m := 25) from colCertDiv_80_13_8.bind2]
  rw [alnId_80 j hj]
  exact fastcode_of_tau ⟨80, by decide⟩ _ _ _
    ((alnId_80 j hj) ▸ Q2.listedAt (⟨80, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨80, by decide⟩ : Fin 148) hj hq).1) colCertDiv_80_13_8_tau_match


theorem leaf_80_13_9 (hp : 9 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 9 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 9 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_9.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_10 (hp : 10 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 10 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 10 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_10.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_11 (hp : 11 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 11 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 11 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_11.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_12 (hp : 12 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 12 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 12 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_12.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_13 (hp : 13 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 13 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 13 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_13.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_14 (hp : 14 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 14 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 14 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_14.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_15 (hp : 15 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 15 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 15 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_15.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_16 (hp : 16 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 16 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 16 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_16.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_17 (hp : 17 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 17 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 17 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_17.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_18 (hp : 18 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 18 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 18 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_18.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_19 (hp : 19 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 19 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 19 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_19.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_20 (hp : 20 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 20 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 20 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_20.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_21 (hp : 21 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 21 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 21 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_21.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_22 (hp : 22 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 22 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 22 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_22.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_23 (hp : 23 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 23 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 23 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_23.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_13_24 (hp : 24 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 24 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp)) T80_13
      hfix80_13 hinj80_13 hcardT80_13
      (fun i => conj_mem_of_fixedPoints _ _ (T80_13 i) (hfix80_13 i) _)
      ⟨80, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 24 hp) Q2.T80_13_2 Q2.hfix80_13_2 Q2.hinj80_13_2
      Q2.hcardT80_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_13_2 i) (Q2.hfix80_13_2 i) _)
      colCert_80_13_24.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T80_19
      hfix80_19 hinj80_19 hcardT80_19
      (fun i => conj_mem_of_fixedPoints _ _ (T80_19 i) (hfix80_19 i) _)
      ⟨80, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T80_19_2 Q2.hfix80_19_2 Q2.hinj80_19_2
      Q2.hcardT80_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_19_2 i) (Q2.hfix80_19_2 i) _)
      colCert_80_19_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T80_19
      hfix80_19 hinj80_19 hcardT80_19
      (fun i => conj_mem_of_fixedPoints _ _ (T80_19 i) (hfix80_19 i) _)
      ⟨80, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T80_19_2 Q2.hfix80_19_2 Q2.hinj80_19_2
      Q2.hcardT80_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_19_2 i) (Q2.hfix80_19_2 i) _)
      colCert_80_19_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T80_19
      hfix80_19 hinj80_19 hcardT80_19
      (fun i => conj_mem_of_fixedPoints _ _ (T80_19 i) (hfix80_19 i) _)
      ⟨80, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T80_19_2 Q2.hfix80_19_2 Q2.hinj80_19_2
      Q2.hcardT80_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_19_2 i) (Q2.hfix80_19_2 i) _)
      colCert_80_19_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T80_19
      hfix80_19 hinj80_19 hcardT80_19
      (fun i => conj_mem_of_fixedPoints _ _ (T80_19 i) (hfix80_19 i) _)
      ⟨80, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T80_19_2 Q2.hfix80_19_2 Q2.hinj80_19_2
      Q2.hcardT80_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_19_2 i) (Q2.hfix80_19_2 i) _)
      colCert_80_19_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T80_19
      hfix80_19 hinj80_19 hcardT80_19
      (fun i => conj_mem_of_fixedPoints _ _ (T80_19 i) (hfix80_19 i) _)
      ⟨80, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T80_19_2 Q2.hfix80_19_2 Q2.hinj80_19_2
      Q2.hcardT80_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_19_2 i) (Q2.hfix80_19_2 i) _)
      colCert_80_19_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T80_19
      hfix80_19 hinj80_19 hcardT80_19
      (fun i => conj_mem_of_fixedPoints _ _ (T80_19 i) (hfix80_19 i) _)
      ⟨80, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T80_19_2 Q2.hfix80_19_2 Q2.hinj80_19_2
      Q2.hcardT80_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_19_2 i) (Q2.hfix80_19_2 i) _)
      colCert_80_19_5.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T80_19
      hfix80_19 hinj80_19 hcardT80_19
      (fun i => conj_mem_of_fixedPoints _ _ (T80_19 i) (hfix80_19 i) _)
      ⟨80, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T80_19_2 Q2.hfix80_19_2 Q2.hinj80_19_2
      Q2.hcardT80_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_19_2 i) (Q2.hfix80_19_2 i) _)
      colCert_80_19_10.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T80_19
      hfix80_19 hinj80_19 hcardT80_19
      (fun i => conj_mem_of_fixedPoints _ _ (T80_19 i) (hfix80_19 i) _)
      ⟨80, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T80_19_2 Q2.hfix80_19_2 Q2.hinj80_19_2
      Q2.hcardT80_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_19_2 i) (Q2.hfix80_19_2 i) _)
      colCert_80_19_15.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T80_19
      hfix80_19 hinj80_19 hcardT80_19
      (fun i => conj_mem_of_fixedPoints _ _ (T80_19 i) (hfix80_19 i) _)
      ⟨80, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T80_19_2 Q2.hfix80_19_2 Q2.hinj80_19_2
      Q2.hcardT80_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_19_2 i) (Q2.hfix80_19_2 i) _)
      colCert_80_19_20.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T80_24
      hfix80_24 hinj80_24 hcardT80_24
      (fun i => conj_mem_of_fixedPoints _ _ (T80_24 i) (hfix80_24 i) _)
      ⟨80, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T80_24_2 Q2.hfix80_24_2 Q2.hinj80_24_2
      Q2.hcardT80_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_24_2 i) (Q2.hfix80_24_2 i) _)
      colCert_80_24_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T80_24
      hfix80_24 hinj80_24 hcardT80_24
      (fun i => conj_mem_of_fixedPoints _ _ (T80_24 i) (hfix80_24 i) _)
      ⟨80, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T80_24_2 Q2.hfix80_24_2 Q2.hinj80_24_2
      Q2.hcardT80_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_24_2 i) (Q2.hfix80_24_2 i) _)
      colCert_80_24_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T80_24
      hfix80_24 hinj80_24 hcardT80_24
      (fun i => conj_mem_of_fixedPoints _ _ (T80_24 i) (hfix80_24 i) _)
      ⟨80, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T80_24_2 Q2.hfix80_24_2 Q2.hinj80_24_2
      Q2.hcardT80_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_24_2 i) (Q2.hfix80_24_2 i) _)
      colCert_80_24_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T80_24
      hfix80_24 hinj80_24 hcardT80_24
      (fun i => conj_mem_of_fixedPoints _ _ (T80_24 i) (hfix80_24 i) _)
      ⟨80, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T80_24_2 Q2.hfix80_24_2 Q2.hinj80_24_2
      Q2.hcardT80_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_24_2 i) (Q2.hfix80_24_2 i) _)
      colCert_80_24_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T80_24
      hfix80_24 hinj80_24 hcardT80_24
      (fun i => conj_mem_of_fixedPoints _ _ (T80_24 i) (hfix80_24 i) _)
      ⟨80, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T80_24_2 Q2.hfix80_24_2 Q2.hinj80_24_2
      Q2.hcardT80_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_24_2 i) (Q2.hfix80_24_2 i) _)
      colCert_80_24_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T80_24
      hfix80_24 hinj80_24 hcardT80_24
      (fun i => conj_mem_of_fixedPoints _ _ (T80_24 i) (hfix80_24 i) _)
      ⟨80, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T80_24_2 Q2.hfix80_24_2 Q2.hinj80_24_2
      Q2.hcardT80_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_24_2 i) (Q2.hfix80_24_2 i) _)
      colCert_80_24_5.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T80_24
      hfix80_24 hinj80_24 hcardT80_24
      (fun i => conj_mem_of_fixedPoints _ _ (T80_24 i) (hfix80_24 i) _)
      ⟨80, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T80_24_2 Q2.hfix80_24_2 Q2.hinj80_24_2
      Q2.hcardT80_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_24_2 i) (Q2.hfix80_24_2 i) _)
      colCert_80_24_10.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T80_24
      hfix80_24 hinj80_24 hcardT80_24
      (fun i => conj_mem_of_fixedPoints _ _ (T80_24 i) (hfix80_24 i) _)
      ⟨80, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T80_24_2 Q2.hfix80_24_2 Q2.hinj80_24_2
      Q2.hcardT80_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_24_2 i) (Q2.hfix80_24_2 i) _)
      colCert_80_24_15.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T80_24
      hfix80_24 hinj80_24 hcardT80_24
      (fun i => conj_mem_of_fixedPoints _ _ (T80_24 i) (hfix80_24 i) _)
      ⟨80, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T80_24_2 Q2.hfix80_24_2 Q2.hinj80_24_2
      Q2.hcardT80_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_24_2 i) (Q2.hfix80_24_2 i) _)
      colCert_80_24_20.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T80_25
      hfix80_25 hinj80_25 hcardT80_25
      (fun i => conj_mem_of_fixedPoints _ _ (T80_25 i) (hfix80_25 i) _)
      ⟨80, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T80_25_2 Q2.hfix80_25_2 Q2.hinj80_25_2
      Q2.hcardT80_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_25_2 i) (Q2.hfix80_25_2 i) _)
      colCert_80_25_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T80_25
      hfix80_25 hinj80_25 hcardT80_25
      (fun i => conj_mem_of_fixedPoints _ _ (T80_25 i) (hfix80_25 i) _)
      ⟨80, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T80_25_2 Q2.hfix80_25_2 Q2.hinj80_25_2
      Q2.hcardT80_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_25_2 i) (Q2.hfix80_25_2 i) _)
      colCert_80_25_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T80_25
      hfix80_25 hinj80_25 hcardT80_25
      (fun i => conj_mem_of_fixedPoints _ _ (T80_25 i) (hfix80_25 i) _)
      ⟨80, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T80_25_2 Q2.hfix80_25_2 Q2.hinj80_25_2
      Q2.hcardT80_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_25_2 i) (Q2.hfix80_25_2 i) _)
      colCert_80_25_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T80_25
      hfix80_25 hinj80_25 hcardT80_25
      (fun i => conj_mem_of_fixedPoints _ _ (T80_25 i) (hfix80_25 i) _)
      ⟨80, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T80_25_2 Q2.hfix80_25_2 Q2.hinj80_25_2
      Q2.hcardT80_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_25_2 i) (Q2.hfix80_25_2 i) _)
      colCert_80_25_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T80_25
      hfix80_25 hinj80_25 hcardT80_25
      (fun i => conj_mem_of_fixedPoints _ _ (T80_25 i) (hfix80_25 i) _)
      ⟨80, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T80_25_2 Q2.hfix80_25_2 Q2.hinj80_25_2
      Q2.hcardT80_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_25_2 i) (Q2.hfix80_25_2 i) _)
      colCert_80_25_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T80_25
      hfix80_25 hinj80_25 hcardT80_25
      (fun i => conj_mem_of_fixedPoints _ _ (T80_25 i) (hfix80_25 i) _)
      ⟨80, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T80_25_2 Q2.hfix80_25_2 Q2.hinj80_25_2
      Q2.hcardT80_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_25_2 i) (Q2.hfix80_25_2 i) _)
      colCert_80_25_5.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T80_25
      hfix80_25 hinj80_25 hcardT80_25
      (fun i => conj_mem_of_fixedPoints _ _ (T80_25 i) (hfix80_25 i) _)
      ⟨80, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T80_25_2 Q2.hfix80_25_2 Q2.hinj80_25_2
      Q2.hcardT80_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_25_2 i) (Q2.hfix80_25_2 i) _)
      colCert_80_25_10.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T80_25
      hfix80_25 hinj80_25 hcardT80_25
      (fun i => conj_mem_of_fixedPoints _ _ (T80_25 i) (hfix80_25 i) _)
      ⟨80, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T80_25_2 Q2.hfix80_25_2 Q2.hinj80_25_2
      Q2.hcardT80_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_25_2 i) (Q2.hfix80_25_2 i) _)
      colCert_80_25_15.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T80_25
      hfix80_25 hinj80_25 hcardT80_25
      (fun i => conj_mem_of_fixedPoints _ _ (T80_25 i) (hfix80_25 i) _)
      ⟨80, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T80_25_2 Q2.hfix80_25_2 Q2.hinj80_25_2
      Q2.hcardT80_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_25_2 i) (Q2.hfix80_25_2 i) _)
      colCert_80_25_20.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T80_26
      hfix80_26 hinj80_26 hcardT80_26
      (fun i => conj_mem_of_fixedPoints _ _ (T80_26 i) (hfix80_26 i) _)
      ⟨80, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T80_26_2 Q2.hfix80_26_2 Q2.hinj80_26_2
      Q2.hcardT80_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_26_2 i) (Q2.hfix80_26_2 i) _)
      colCert_80_26_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T80_26
      hfix80_26 hinj80_26 hcardT80_26
      (fun i => conj_mem_of_fixedPoints _ _ (T80_26 i) (hfix80_26 i) _)
      ⟨80, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T80_26_2 Q2.hfix80_26_2 Q2.hinj80_26_2
      Q2.hcardT80_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_26_2 i) (Q2.hfix80_26_2 i) _)
      colCert_80_26_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T80_26
      hfix80_26 hinj80_26 hcardT80_26
      (fun i => conj_mem_of_fixedPoints _ _ (T80_26 i) (hfix80_26 i) _)
      ⟨80, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T80_26_2 Q2.hfix80_26_2 Q2.hinj80_26_2
      Q2.hcardT80_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_26_2 i) (Q2.hfix80_26_2 i) _)
      colCert_80_26_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T80_26
      hfix80_26 hinj80_26 hcardT80_26
      (fun i => conj_mem_of_fixedPoints _ _ (T80_26 i) (hfix80_26 i) _)
      ⟨80, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T80_26_2 Q2.hfix80_26_2 Q2.hinj80_26_2
      Q2.hcardT80_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_26_2 i) (Q2.hfix80_26_2 i) _)
      colCert_80_26_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T80_26
      hfix80_26 hinj80_26 hcardT80_26
      (fun i => conj_mem_of_fixedPoints _ _ (T80_26 i) (hfix80_26 i) _)
      ⟨80, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T80_26_2 Q2.hfix80_26_2 Q2.hinj80_26_2
      Q2.hcardT80_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_26_2 i) (Q2.hfix80_26_2 i) _)
      colCert_80_26_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T80_26
      hfix80_26 hinj80_26 hcardT80_26
      (fun i => conj_mem_of_fixedPoints _ _ (T80_26 i) (hfix80_26 i) _)
      ⟨80, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T80_26_2 Q2.hfix80_26_2 Q2.hinj80_26_2
      Q2.hcardT80_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_26_2 i) (Q2.hfix80_26_2 i) _)
      colCert_80_26_5.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T80_26
      hfix80_26 hinj80_26 hcardT80_26
      (fun i => conj_mem_of_fixedPoints _ _ (T80_26 i) (hfix80_26 i) _)
      ⟨80, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T80_26_2 Q2.hfix80_26_2 Q2.hinj80_26_2
      Q2.hcardT80_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_26_2 i) (Q2.hfix80_26_2 i) _)
      colCert_80_26_10.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T80_26
      hfix80_26 hinj80_26 hcardT80_26
      (fun i => conj_mem_of_fixedPoints _ _ (T80_26 i) (hfix80_26 i) _)
      ⟨80, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T80_26_2 Q2.hfix80_26_2 Q2.hinj80_26_2
      Q2.hcardT80_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_26_2 i) (Q2.hfix80_26_2 i) _)
      colCert_80_26_15.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T80_26
      hfix80_26 hinj80_26 hcardT80_26
      (fun i => conj_mem_of_fixedPoints _ _ (T80_26 i) (hfix80_26 i) _)
      ⟨80, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T80_26_2 Q2.hfix80_26_2 Q2.hinj80_26_2
      Q2.hcardT80_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_26_2 i) (Q2.hfix80_26_2 i) _)
      colCert_80_26_20.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T80_27
      hfix80_27 hinj80_27 hcardT80_27
      (fun i => conj_mem_of_fixedPoints _ _ (T80_27 i) (hfix80_27 i) _)
      ⟨80, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T80_27_2 Q2.hfix80_27_2 Q2.hinj80_27_2
      Q2.hcardT80_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_27_2 i) (Q2.hfix80_27_2 i) _)
      colCert_80_27_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T80_27
      hfix80_27 hinj80_27 hcardT80_27
      (fun i => conj_mem_of_fixedPoints _ _ (T80_27 i) (hfix80_27 i) _)
      ⟨80, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T80_27_2 Q2.hfix80_27_2 Q2.hinj80_27_2
      Q2.hcardT80_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_27_2 i) (Q2.hfix80_27_2 i) _)
      colCert_80_27_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T80_27
      hfix80_27 hinj80_27 hcardT80_27
      (fun i => conj_mem_of_fixedPoints _ _ (T80_27 i) (hfix80_27 i) _)
      ⟨80, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T80_27_2 Q2.hfix80_27_2 Q2.hinj80_27_2
      Q2.hcardT80_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_27_2 i) (Q2.hfix80_27_2 i) _)
      colCert_80_27_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T80_27
      hfix80_27 hinj80_27 hcardT80_27
      (fun i => conj_mem_of_fixedPoints _ _ (T80_27 i) (hfix80_27 i) _)
      ⟨80, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T80_27_2 Q2.hfix80_27_2 Q2.hinj80_27_2
      Q2.hcardT80_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_27_2 i) (Q2.hfix80_27_2 i) _)
      colCert_80_27_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T80_27
      hfix80_27 hinj80_27 hcardT80_27
      (fun i => conj_mem_of_fixedPoints _ _ (T80_27 i) (hfix80_27 i) _)
      ⟨80, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T80_27_2 Q2.hfix80_27_2 Q2.hinj80_27_2
      Q2.hcardT80_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_27_2 i) (Q2.hfix80_27_2 i) _)
      colCert_80_27_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T80_27
      hfix80_27 hinj80_27 hcardT80_27
      (fun i => conj_mem_of_fixedPoints _ _ (T80_27 i) (hfix80_27 i) _)
      ⟨80, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T80_27_2 Q2.hfix80_27_2 Q2.hinj80_27_2
      Q2.hcardT80_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_27_2 i) (Q2.hfix80_27_2 i) _)
      colCert_80_27_5.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T80_27
      hfix80_27 hinj80_27 hcardT80_27
      (fun i => conj_mem_of_fixedPoints _ _ (T80_27 i) (hfix80_27 i) _)
      ⟨80, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T80_27_2 Q2.hfix80_27_2 Q2.hinj80_27_2
      Q2.hcardT80_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_27_2 i) (Q2.hfix80_27_2 i) _)
      colCert_80_27_10.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T80_27
      hfix80_27 hinj80_27 hcardT80_27
      (fun i => conj_mem_of_fixedPoints _ _ (T80_27 i) (hfix80_27 i) _)
      ⟨80, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T80_27_2 Q2.hfix80_27_2 Q2.hinj80_27_2
      Q2.hcardT80_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_27_2 i) (Q2.hfix80_27_2 i) _)
      colCert_80_27_15.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T80_27
      hfix80_27 hinj80_27 hcardT80_27
      (fun i => conj_mem_of_fixedPoints _ _ (T80_27 i) (hfix80_27 i) _)
      ⟨80, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T80_27_2 Q2.hfix80_27_2 Q2.hinj80_27_2
      Q2.hcardT80_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_27_2 i) (Q2.hfix80_27_2 i) _)
      colCert_80_27_20.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T80_53
      hfix80_53 hinj80_53 hcardT80_53
      (fun i => conj_mem_of_fixedPoints _ _ (T80_53 i) (hfix80_53 i) _)
      ⟨80, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T80_53_2 Q2.hfix80_53_2 Q2.hinj80_53_2
      Q2.hcardT80_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_53_2 i) (Q2.hfix80_53_2 i) _)
      colCert_80_53_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T80_53
      hfix80_53 hinj80_53 hcardT80_53
      (fun i => conj_mem_of_fixedPoints _ _ (T80_53 i) (hfix80_53 i) _)
      ⟨80, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T80_53_2 Q2.hfix80_53_2 Q2.hinj80_53_2
      Q2.hcardT80_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_53_2 i) (Q2.hfix80_53_2 i) _)
      colCert_80_53_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T80_53
      hfix80_53 hinj80_53 hcardT80_53
      (fun i => conj_mem_of_fixedPoints _ _ (T80_53 i) (hfix80_53 i) _)
      ⟨80, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T80_53_2 Q2.hfix80_53_2 Q2.hinj80_53_2
      Q2.hcardT80_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_53_2 i) (Q2.hfix80_53_2 i) _)
      colCert_80_53_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T80_53
      hfix80_53 hinj80_53 hcardT80_53
      (fun i => conj_mem_of_fixedPoints _ _ (T80_53 i) (hfix80_53 i) _)
      ⟨80, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T80_53_2 Q2.hfix80_53_2 Q2.hinj80_53_2
      Q2.hcardT80_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_53_2 i) (Q2.hfix80_53_2 i) _)
      colCert_80_53_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T80_53
      hfix80_53 hinj80_53 hcardT80_53
      (fun i => conj_mem_of_fixedPoints _ _ (T80_53 i) (hfix80_53 i) _)
      ⟨80, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T80_53_2 Q2.hfix80_53_2 Q2.hinj80_53_2
      Q2.hcardT80_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_53_2 i) (Q2.hfix80_53_2 i) _)
      colCert_80_53_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T80_53
      hfix80_53 hinj80_53 hcardT80_53
      (fun i => conj_mem_of_fixedPoints _ _ (T80_53 i) (hfix80_53 i) _)
      ⟨80, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T80_53_2 Q2.hfix80_53_2 Q2.hinj80_53_2
      Q2.hcardT80_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_53_2 i) (Q2.hfix80_53_2 i) _)
      colCert_80_53_5.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T80_53
      hfix80_53 hinj80_53 hcardT80_53
      (fun i => conj_mem_of_fixedPoints _ _ (T80_53 i) (hfix80_53 i) _)
      ⟨80, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T80_53_2 Q2.hfix80_53_2 Q2.hinj80_53_2
      Q2.hcardT80_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_53_2 i) (Q2.hfix80_53_2 i) _)
      colCert_80_53_10.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T80_53
      hfix80_53 hinj80_53 hcardT80_53
      (fun i => conj_mem_of_fixedPoints _ _ (T80_53 i) (hfix80_53 i) _)
      ⟨80, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T80_53_2 Q2.hfix80_53_2 Q2.hinj80_53_2
      Q2.hcardT80_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_53_2 i) (Q2.hfix80_53_2 i) _)
      colCert_80_53_15.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T80_53
      hfix80_53 hinj80_53 hcardT80_53
      (fun i => conj_mem_of_fixedPoints _ _ (T80_53 i) (hfix80_53 i) _)
      ⟨80, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T80_53_2 Q2.hfix80_53_2 Q2.hinj80_53_2
      Q2.hcardT80_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_53_2 i) (Q2.hfix80_53_2 i) _)
      colCert_80_53_20.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_0 (hp : 0 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 0 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 0 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_0.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_1 (hp : 1 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 1 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 1 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_1.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_2 (hp : 2 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 2 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 2 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_2.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_3 (hp : 3 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 3 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 3 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_3.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_4 (hp : 4 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 4 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 4 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_4.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_5 (hp : 5 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 5 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 5 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_5.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_10 (hp : 10 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 10 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 10 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_10.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_15 (hp : 15 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 15 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 15 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_15.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_20 (hp : 20 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 20 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 20 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_20.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_25 (hp : 25 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 25 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 25 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_25.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_30 (hp : 30 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 30 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 30 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_30.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_35 (hp : 35 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 35 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 35 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_35.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_40 (hp : 40 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 40 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 40 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_40.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_45 (hp : 45 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 45 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 45 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_45.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_50 (hp : 50 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 50 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 50 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_50.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_55 (hp : 55 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 55 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 55 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_55.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_60 (hp : 60 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 60 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 60 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_60.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_65 (hp : 65 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 65 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 65 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_65.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_70 (hp : 70 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 70 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 70 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_70.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_75 (hp : 75 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 75 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 75 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_75.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_80 (hp : 80 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 80 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 80 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_80.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_85 (hp : 85 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 85 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 85 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_85.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_90 (hp : 90 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 90 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 90 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_90.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_95 (hp : 95 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 95 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 95 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_95.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_100 (hp : 100 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 100 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 100 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_100.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_105 (hp : 105 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 105 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 105 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_105.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_110 (hp : 110 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 110 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 110 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_110.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_115 (hp : 115 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 115 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 115 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_115.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_80_80_120 (hp : 120 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 80 []).length)
    (hq : (normIsRep.getD 80 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 120 hp)
        (rowE2 (⟨80, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp))
        (rowE1 (⟨80, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨80, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨80, by decide⟩ (listedAt ⟨80, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp)) T80_80
      hfix80_80 hinj80_80 hcardT80_80
      (fun i => conj_mem_of_fixedPoints _ _ (T80_80 i) (hfix80_80 i) _)
      ⟨80, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨80, by decide⟩ (Q2.listedAt ⟨80, by decide⟩
        (alnCheck_rep ⟨80, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 120 hp) Q2.T80_80_2 Q2.hfix80_80_2 Q2.hinj80_80_2
      Q2.hcardT80_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T80_80_2 i) (Q2.hfix80_80_2 i) _)
      colCert_80_80_120.hD ?_).symm
  rw [alnId_80 j hj]


theorem leaf_81_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T81_2
      hfix81_2 hinj81_2 hcardT81_2
      (fun i => conj_mem_of_fixedPoints _ _ (T81_2 i) (hfix81_2 i) _)
      ⟨81, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T81_2_2 Q2.hfix81_2_2 Q2.hinj81_2_2
      Q2.hcardT81_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_2_2 i) (Q2.hfix81_2_2 i) _)
      colCert_81_2_0.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T81_2
      hfix81_2 hinj81_2 hcardT81_2
      (fun i => conj_mem_of_fixedPoints _ _ (T81_2 i) (hfix81_2 i) _)
      ⟨81, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T81_2_2 Q2.hfix81_2_2 Q2.hinj81_2_2
      Q2.hcardT81_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_2_2 i) (Q2.hfix81_2_2 i) _)
      colCert_81_2_1.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T81_2
      hfix81_2 hinj81_2 hcardT81_2
      (fun i => conj_mem_of_fixedPoints _ _ (T81_2 i) (hfix81_2 i) _)
      ⟨81, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T81_2_2 Q2.hfix81_2_2 Q2.hinj81_2_2
      Q2.hcardT81_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_2_2 i) (Q2.hfix81_2_2 i) _)
      colCert_81_2_2.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T81_2
      hfix81_2 hinj81_2 hcardT81_2
      (fun i => conj_mem_of_fixedPoints _ _ (T81_2 i) (hfix81_2 i) _)
      ⟨81, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T81_2_2 Q2.hfix81_2_2 Q2.hinj81_2_2
      Q2.hcardT81_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_2_2 i) (Q2.hfix81_2_2 i) _)
      colCert_81_2_3.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T81_2
      hfix81_2 hinj81_2 hcardT81_2
      (fun i => conj_mem_of_fixedPoints _ _ (T81_2 i) (hfix81_2 i) _)
      ⟨81, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T81_2_2 Q2.hfix81_2_2 Q2.hinj81_2_2
      Q2.hcardT81_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_2_2 i) (Q2.hfix81_2_2 i) _)
      colCert_81_2_4.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T81_10
      hfix81_10 hinj81_10 hcardT81_10
      (fun i => conj_mem_of_fixedPoints _ _ (T81_10 i) (hfix81_10 i) _)
      ⟨81, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T81_10_2 Q2.hfix81_10_2 Q2.hinj81_10_2
      Q2.hcardT81_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_10_2 i) (Q2.hfix81_10_2 i) _)
      colCert_81_10_0.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T81_10
      hfix81_10 hinj81_10 hcardT81_10
      (fun i => conj_mem_of_fixedPoints _ _ (T81_10 i) (hfix81_10 i) _)
      ⟨81, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T81_10_2 Q2.hfix81_10_2 Q2.hinj81_10_2
      Q2.hcardT81_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_10_2 i) (Q2.hfix81_10_2 i) _)
      colCert_81_10_1.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T81_10
      hfix81_10 hinj81_10 hcardT81_10
      (fun i => conj_mem_of_fixedPoints _ _ (T81_10 i) (hfix81_10 i) _)
      ⟨81, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T81_10_2 Q2.hfix81_10_2 Q2.hinj81_10_2
      Q2.hcardT81_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_10_2 i) (Q2.hfix81_10_2 i) _)
      colCert_81_10_2.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T81_10
      hfix81_10 hinj81_10 hcardT81_10
      (fun i => conj_mem_of_fixedPoints _ _ (T81_10 i) (hfix81_10 i) _)
      ⟨81, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T81_10_2 Q2.hfix81_10_2 Q2.hinj81_10_2
      Q2.hcardT81_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_10_2 i) (Q2.hfix81_10_2 i) _)
      colCert_81_10_3.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T81_10
      hfix81_10 hinj81_10 hcardT81_10
      (fun i => conj_mem_of_fixedPoints _ _ (T81_10 i) (hfix81_10 i) _)
      ⟨81, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T81_10_2 Q2.hfix81_10_2 Q2.hinj81_10_2
      Q2.hcardT81_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_10_2 i) (Q2.hfix81_10_2 i) _)
      colCert_81_10_4.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T81_12
      hfix81_12 hinj81_12 hcardT81_12
      (fun i => conj_mem_of_fixedPoints _ _ (T81_12 i) (hfix81_12 i) _)
      ⟨81, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T81_12_2 Q2.hfix81_12_2 Q2.hinj81_12_2
      Q2.hcardT81_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_12_2 i) (Q2.hfix81_12_2 i) _)
      colCert_81_12_0.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T81_12
      hfix81_12 hinj81_12 hcardT81_12
      (fun i => conj_mem_of_fixedPoints _ _ (T81_12 i) (hfix81_12 i) _)
      ⟨81, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T81_12_2 Q2.hfix81_12_2 Q2.hinj81_12_2
      Q2.hcardT81_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_12_2 i) (Q2.hfix81_12_2 i) _)
      colCert_81_12_1.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T81_12
      hfix81_12 hinj81_12 hcardT81_12
      (fun i => conj_mem_of_fixedPoints _ _ (T81_12 i) (hfix81_12 i) _)
      ⟨81, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T81_12_2 Q2.hfix81_12_2 Q2.hinj81_12_2
      Q2.hcardT81_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_12_2 i) (Q2.hfix81_12_2 i) _)
      colCert_81_12_2.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T81_12
      hfix81_12 hinj81_12 hcardT81_12
      (fun i => conj_mem_of_fixedPoints _ _ (T81_12 i) (hfix81_12 i) _)
      ⟨81, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T81_12_2 Q2.hfix81_12_2 Q2.hinj81_12_2
      Q2.hcardT81_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_12_2 i) (Q2.hfix81_12_2 i) _)
      colCert_81_12_3.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T81_12
      hfix81_12 hinj81_12 hcardT81_12
      (fun i => conj_mem_of_fixedPoints _ _ (T81_12 i) (hfix81_12 i) _)
      ⟨81, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T81_12_2 Q2.hfix81_12_2 Q2.hinj81_12_2
      Q2.hcardT81_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_12_2 i) (Q2.hfix81_12_2 i) _)
      colCert_81_12_4.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T81_20
      hfix81_20 hinj81_20 hcardT81_20
      (fun i => conj_mem_of_fixedPoints _ _ (T81_20 i) (hfix81_20 i) _)
      ⟨81, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T81_20_2 Q2.hfix81_20_2 Q2.hinj81_20_2
      Q2.hcardT81_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_20_2 i) (Q2.hfix81_20_2 i) _)
      colCert_81_20_0.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T81_20
      hfix81_20 hinj81_20 hcardT81_20
      (fun i => conj_mem_of_fixedPoints _ _ (T81_20 i) (hfix81_20 i) _)
      ⟨81, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T81_20_2 Q2.hfix81_20_2 Q2.hinj81_20_2
      Q2.hcardT81_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_20_2 i) (Q2.hfix81_20_2 i) _)
      colCert_81_20_1.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T81_20
      hfix81_20 hinj81_20 hcardT81_20
      (fun i => conj_mem_of_fixedPoints _ _ (T81_20 i) (hfix81_20 i) _)
      ⟨81, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T81_20_2 Q2.hfix81_20_2 Q2.hinj81_20_2
      Q2.hcardT81_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_20_2 i) (Q2.hfix81_20_2 i) _)
      colCert_81_20_2.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T81_20
      hfix81_20 hinj81_20 hcardT81_20
      (fun i => conj_mem_of_fixedPoints _ _ (T81_20 i) (hfix81_20 i) _)
      ⟨81, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T81_20_2 Q2.hfix81_20_2 Q2.hinj81_20_2
      Q2.hcardT81_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_20_2 i) (Q2.hfix81_20_2 i) _)
      colCert_81_20_3.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T81_20
      hfix81_20 hinj81_20 hcardT81_20
      (fun i => conj_mem_of_fixedPoints _ _ (T81_20 i) (hfix81_20 i) _)
      ⟨81, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T81_20_2 Q2.hfix81_20_2 Q2.hinj81_20_2
      Q2.hcardT81_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_20_2 i) (Q2.hfix81_20_2 i) _)
      colCert_81_20_4.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T81_20
      hfix81_20 hinj81_20 hcardT81_20
      (fun i => conj_mem_of_fixedPoints _ _ (T81_20 i) (hfix81_20 i) _)
      ⟨81, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T81_20_2 Q2.hfix81_20_2 Q2.hinj81_20_2
      Q2.hcardT81_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_20_2 i) (Q2.hfix81_20_2 i) _)
      colCert_81_20_5.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T81_20
      hfix81_20 hinj81_20 hcardT81_20
      (fun i => conj_mem_of_fixedPoints _ _ (T81_20 i) (hfix81_20 i) _)
      ⟨81, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T81_20_2 Q2.hfix81_20_2 Q2.hinj81_20_2
      Q2.hcardT81_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_20_2 i) (Q2.hfix81_20_2 i) _)
      colCert_81_20_10.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T81_20
      hfix81_20 hinj81_20 hcardT81_20
      (fun i => conj_mem_of_fixedPoints _ _ (T81_20 i) (hfix81_20 i) _)
      ⟨81, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T81_20_2 Q2.hfix81_20_2 Q2.hinj81_20_2
      Q2.hcardT81_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_20_2 i) (Q2.hfix81_20_2 i) _)
      colCert_81_20_15.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T81_20
      hfix81_20 hinj81_20 hcardT81_20
      (fun i => conj_mem_of_fixedPoints _ _ (T81_20 i) (hfix81_20 i) _)
      ⟨81, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T81_20_2 Q2.hfix81_20_2 Q2.hinj81_20_2
      Q2.hcardT81_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_20_2 i) (Q2.hfix81_20_2 i) _)
      colCert_81_20_20.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T81_53
      hfix81_53 hinj81_53 hcardT81_53
      (fun i => conj_mem_of_fixedPoints _ _ (T81_53 i) (hfix81_53 i) _)
      ⟨81, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T81_53_2 Q2.hfix81_53_2 Q2.hinj81_53_2
      Q2.hcardT81_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_53_2 i) (Q2.hfix81_53_2 i) _)
      colCert_81_53_0.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T81_53
      hfix81_53 hinj81_53 hcardT81_53
      (fun i => conj_mem_of_fixedPoints _ _ (T81_53 i) (hfix81_53 i) _)
      ⟨81, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T81_53_2 Q2.hfix81_53_2 Q2.hinj81_53_2
      Q2.hcardT81_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_53_2 i) (Q2.hfix81_53_2 i) _)
      colCert_81_53_1.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T81_53
      hfix81_53 hinj81_53 hcardT81_53
      (fun i => conj_mem_of_fixedPoints _ _ (T81_53 i) (hfix81_53 i) _)
      ⟨81, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T81_53_2 Q2.hfix81_53_2 Q2.hinj81_53_2
      Q2.hcardT81_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_53_2 i) (Q2.hfix81_53_2 i) _)
      colCert_81_53_2.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T81_53
      hfix81_53 hinj81_53 hcardT81_53
      (fun i => conj_mem_of_fixedPoints _ _ (T81_53 i) (hfix81_53 i) _)
      ⟨81, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T81_53_2 Q2.hfix81_53_2 Q2.hinj81_53_2
      Q2.hcardT81_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_53_2 i) (Q2.hfix81_53_2 i) _)
      colCert_81_53_3.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T81_53
      hfix81_53 hinj81_53 hcardT81_53
      (fun i => conj_mem_of_fixedPoints _ _ (T81_53 i) (hfix81_53 i) _)
      ⟨81, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T81_53_2 Q2.hfix81_53_2 Q2.hinj81_53_2
      Q2.hcardT81_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_53_2 i) (Q2.hfix81_53_2 i) _)
      colCert_81_53_4.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T81_53
      hfix81_53 hinj81_53 hcardT81_53
      (fun i => conj_mem_of_fixedPoints _ _ (T81_53 i) (hfix81_53 i) _)
      ⟨81, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T81_53_2 Q2.hfix81_53_2 Q2.hinj81_53_2
      Q2.hcardT81_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_53_2 i) (Q2.hfix81_53_2 i) _)
      colCert_81_53_5.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T81_53
      hfix81_53 hinj81_53 hcardT81_53
      (fun i => conj_mem_of_fixedPoints _ _ (T81_53 i) (hfix81_53 i) _)
      ⟨81, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T81_53_2 Q2.hfix81_53_2 Q2.hinj81_53_2
      Q2.hcardT81_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_53_2 i) (Q2.hfix81_53_2 i) _)
      colCert_81_53_10.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T81_53
      hfix81_53 hinj81_53 hcardT81_53
      (fun i => conj_mem_of_fixedPoints _ _ (T81_53 i) (hfix81_53 i) _)
      ⟨81, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T81_53_2 Q2.hfix81_53_2 Q2.hinj81_53_2
      Q2.hcardT81_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_53_2 i) (Q2.hfix81_53_2 i) _)
      colCert_81_53_15.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T81_53
      hfix81_53 hinj81_53 hcardT81_53
      (fun i => conj_mem_of_fixedPoints _ _ (T81_53 i) (hfix81_53 i) _)
      ⟨81, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T81_53_2 Q2.hfix81_53_2 Q2.hinj81_53_2
      Q2.hcardT81_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_53_2 i) (Q2.hfix81_53_2 i) _)
      colCert_81_53_20.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_81_0 (hp : 0 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 0 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp)) T81_81
      hfix81_81 hinj81_81 hcardT81_81
      (fun i => conj_mem_of_fixedPoints _ _ (T81_81 i) (hfix81_81 i) _)
      ⟨81, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 0 hp) Q2.T81_81_2 Q2.hfix81_81_2 Q2.hinj81_81_2
      Q2.hcardT81_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_81_2 i) (Q2.hfix81_81_2 i) _)
      colCert_81_81_0.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_81_1 (hp : 1 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 1 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp)) T81_81
      hfix81_81 hinj81_81 hcardT81_81
      (fun i => conj_mem_of_fixedPoints _ _ (T81_81 i) (hfix81_81 i) _)
      ⟨81, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 1 hp) Q2.T81_81_2 Q2.hfix81_81_2 Q2.hinj81_81_2
      Q2.hcardT81_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_81_2 i) (Q2.hfix81_81_2 i) _)
      colCert_81_81_1.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_81_2 (hp : 2 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 2 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp)) T81_81
      hfix81_81 hinj81_81 hcardT81_81
      (fun i => conj_mem_of_fixedPoints _ _ (T81_81 i) (hfix81_81 i) _)
      ⟨81, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 2 hp) Q2.T81_81_2 Q2.hfix81_81_2 Q2.hinj81_81_2
      Q2.hcardT81_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_81_2 i) (Q2.hfix81_81_2 i) _)
      colCert_81_81_2.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_81_3 (hp : 3 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 3 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp)) T81_81
      hfix81_81 hinj81_81 hcardT81_81
      (fun i => conj_mem_of_fixedPoints _ _ (T81_81 i) (hfix81_81 i) _)
      ⟨81, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 3 hp) Q2.T81_81_2 Q2.hfix81_81_2 Q2.hinj81_81_2
      Q2.hcardT81_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_81_2 i) (Q2.hfix81_81_2 i) _)
      colCert_81_81_3.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_81_4 (hp : 4 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 4 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp)) T81_81
      hfix81_81 hinj81_81 hcardT81_81
      (fun i => conj_mem_of_fixedPoints _ _ (T81_81 i) (hfix81_81 i) _)
      ⟨81, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 4 hp) Q2.T81_81_2 Q2.hfix81_81_2 Q2.hinj81_81_2
      Q2.hcardT81_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_81_2 i) (Q2.hfix81_81_2 i) _)
      colCert_81_81_4.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_81_5 (hp : 5 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 5 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp)) T81_81
      hfix81_81 hinj81_81 hcardT81_81
      (fun i => conj_mem_of_fixedPoints _ _ (T81_81 i) (hfix81_81 i) _)
      ⟨81, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 5 hp) Q2.T81_81_2 Q2.hfix81_81_2 Q2.hinj81_81_2
      Q2.hcardT81_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_81_2 i) (Q2.hfix81_81_2 i) _)
      colCert_81_81_5.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_81_10 (hp : 10 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 10 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp)) T81_81
      hfix81_81 hinj81_81 hcardT81_81
      (fun i => conj_mem_of_fixedPoints _ _ (T81_81 i) (hfix81_81 i) _)
      ⟨81, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 10 hp) Q2.T81_81_2 Q2.hfix81_81_2 Q2.hinj81_81_2
      Q2.hcardT81_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_81_2 i) (Q2.hfix81_81_2 i) _)
      colCert_81_81_10.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_81_15 (hp : 15 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 15 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp)) T81_81
      hfix81_81 hinj81_81 hcardT81_81
      (fun i => conj_mem_of_fixedPoints _ _ (T81_81 i) (hfix81_81 i) _)
      ⟨81, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 15 hp) Q2.T81_81_2 Q2.hfix81_81_2 Q2.hinj81_81_2
      Q2.hcardT81_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_81_2 i) (Q2.hfix81_81_2 i) _)
      colCert_81_81_15.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_81_81_20 (hp : 20 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 81 []).length)
    (hq : (normIsRep.getD 81 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 20 hp)
        (rowE2 (⟨81, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp))
        (rowE1 (⟨81, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨81, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨81, by decide⟩ (listedAt ⟨81, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp)) T81_81
      hfix81_81 hinj81_81 hcardT81_81
      (fun i => conj_mem_of_fixedPoints _ _ (T81_81 i) (hfix81_81 i) _)
      ⟨81, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨81, by decide⟩ (Q2.listedAt ⟨81, by decide⟩
        (alnCheck_rep ⟨81, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 20 hp) Q2.T81_81_2 Q2.hfix81_81_2 Q2.hinj81_81_2
      Q2.hcardT81_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T81_81_2 i) (Q2.hfix81_81_2 i) _)
      colCert_81_81_20.hD ?_).symm
  rw [alnId_81 j hj]


theorem leaf_82_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T82_3
      hfix82_3 hinj82_3 hcardT82_3
      (fun i => conj_mem_of_fixedPoints _ _ (T82_3 i) (hfix82_3 i) _)
      ⟨82, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T82_3_2 Q2.hfix82_3_2 Q2.hinj82_3_2
      Q2.hcardT82_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_3_2 i) (Q2.hfix82_3_2 i) _)
      colCert_82_3_0.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T82_3
      hfix82_3 hinj82_3 hcardT82_3
      (fun i => conj_mem_of_fixedPoints _ _ (T82_3 i) (hfix82_3 i) _)
      ⟨82, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T82_3_2 Q2.hfix82_3_2 Q2.hinj82_3_2
      Q2.hcardT82_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_3_2 i) (Q2.hfix82_3_2 i) _)
      colCert_82_3_1.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T82_3
      hfix82_3 hinj82_3 hcardT82_3
      (fun i => conj_mem_of_fixedPoints _ _ (T82_3 i) (hfix82_3 i) _)
      ⟨82, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T82_3_2 Q2.hfix82_3_2 Q2.hinj82_3_2
      Q2.hcardT82_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_3_2 i) (Q2.hfix82_3_2 i) _)
      colCert_82_3_2.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T82_3
      hfix82_3 hinj82_3 hcardT82_3
      (fun i => conj_mem_of_fixedPoints _ _ (T82_3 i) (hfix82_3 i) _)
      ⟨82, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T82_3_2 Q2.hfix82_3_2 Q2.hinj82_3_2
      Q2.hcardT82_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_3_2 i) (Q2.hfix82_3_2 i) _)
      colCert_82_3_3.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T82_3
      hfix82_3 hinj82_3 hcardT82_3
      (fun i => conj_mem_of_fixedPoints _ _ (T82_3 i) (hfix82_3 i) _)
      ⟨82, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T82_3_2 Q2.hfix82_3_2 Q2.hinj82_3_2
      Q2.hcardT82_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_3_2 i) (Q2.hfix82_3_2 i) _)
      colCert_82_3_4.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T82_10
      hfix82_10 hinj82_10 hcardT82_10
      (fun i => conj_mem_of_fixedPoints _ _ (T82_10 i) (hfix82_10 i) _)
      ⟨82, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T82_10_2 Q2.hfix82_10_2 Q2.hinj82_10_2
      Q2.hcardT82_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_10_2 i) (Q2.hfix82_10_2 i) _)
      colCert_82_10_0.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T82_10
      hfix82_10 hinj82_10 hcardT82_10
      (fun i => conj_mem_of_fixedPoints _ _ (T82_10 i) (hfix82_10 i) _)
      ⟨82, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T82_10_2 Q2.hfix82_10_2 Q2.hinj82_10_2
      Q2.hcardT82_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_10_2 i) (Q2.hfix82_10_2 i) _)
      colCert_82_10_1.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T82_10
      hfix82_10 hinj82_10 hcardT82_10
      (fun i => conj_mem_of_fixedPoints _ _ (T82_10 i) (hfix82_10 i) _)
      ⟨82, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T82_10_2 Q2.hfix82_10_2 Q2.hinj82_10_2
      Q2.hcardT82_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_10_2 i) (Q2.hfix82_10_2 i) _)
      colCert_82_10_2.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T82_10
      hfix82_10 hinj82_10 hcardT82_10
      (fun i => conj_mem_of_fixedPoints _ _ (T82_10 i) (hfix82_10 i) _)
      ⟨82, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T82_10_2 Q2.hfix82_10_2 Q2.hinj82_10_2
      Q2.hcardT82_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_10_2 i) (Q2.hfix82_10_2 i) _)
      colCert_82_10_3.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T82_10
      hfix82_10 hinj82_10 hcardT82_10
      (fun i => conj_mem_of_fixedPoints _ _ (T82_10 i) (hfix82_10 i) _)
      ⟨82, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T82_10_2 Q2.hfix82_10_2 Q2.hinj82_10_2
      Q2.hcardT82_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_10_2 i) (Q2.hfix82_10_2 i) _)
      colCert_82_10_4.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T82_12
      hfix82_12 hinj82_12 hcardT82_12
      (fun i => conj_mem_of_fixedPoints _ _ (T82_12 i) (hfix82_12 i) _)
      ⟨82, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T82_12_2 Q2.hfix82_12_2 Q2.hinj82_12_2
      Q2.hcardT82_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_12_2 i) (Q2.hfix82_12_2 i) _)
      colCert_82_12_0.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T82_12
      hfix82_12 hinj82_12 hcardT82_12
      (fun i => conj_mem_of_fixedPoints _ _ (T82_12 i) (hfix82_12 i) _)
      ⟨82, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T82_12_2 Q2.hfix82_12_2 Q2.hinj82_12_2
      Q2.hcardT82_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_12_2 i) (Q2.hfix82_12_2 i) _)
      colCert_82_12_1.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T82_12
      hfix82_12 hinj82_12 hcardT82_12
      (fun i => conj_mem_of_fixedPoints _ _ (T82_12 i) (hfix82_12 i) _)
      ⟨82, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T82_12_2 Q2.hfix82_12_2 Q2.hinj82_12_2
      Q2.hcardT82_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_12_2 i) (Q2.hfix82_12_2 i) _)
      colCert_82_12_2.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T82_12
      hfix82_12 hinj82_12 hcardT82_12
      (fun i => conj_mem_of_fixedPoints _ _ (T82_12 i) (hfix82_12 i) _)
      ⟨82, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T82_12_2 Q2.hfix82_12_2 Q2.hinj82_12_2
      Q2.hcardT82_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_12_2 i) (Q2.hfix82_12_2 i) _)
      colCert_82_12_3.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T82_12
      hfix82_12 hinj82_12 hcardT82_12
      (fun i => conj_mem_of_fixedPoints _ _ (T82_12 i) (hfix82_12 i) _)
      ⟨82, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T82_12_2 Q2.hfix82_12_2 Q2.hinj82_12_2
      Q2.hcardT82_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_12_2 i) (Q2.hfix82_12_2 i) _)
      colCert_82_12_4.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T82_21
      hfix82_21 hinj82_21 hcardT82_21
      (fun i => conj_mem_of_fixedPoints _ _ (T82_21 i) (hfix82_21 i) _)
      ⟨82, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T82_21_2 Q2.hfix82_21_2 Q2.hinj82_21_2
      Q2.hcardT82_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_21_2 i) (Q2.hfix82_21_2 i) _)
      colCert_82_21_0.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T82_21
      hfix82_21 hinj82_21 hcardT82_21
      (fun i => conj_mem_of_fixedPoints _ _ (T82_21 i) (hfix82_21 i) _)
      ⟨82, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T82_21_2 Q2.hfix82_21_2 Q2.hinj82_21_2
      Q2.hcardT82_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_21_2 i) (Q2.hfix82_21_2 i) _)
      colCert_82_21_1.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T82_21
      hfix82_21 hinj82_21 hcardT82_21
      (fun i => conj_mem_of_fixedPoints _ _ (T82_21 i) (hfix82_21 i) _)
      ⟨82, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T82_21_2 Q2.hfix82_21_2 Q2.hinj82_21_2
      Q2.hcardT82_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_21_2 i) (Q2.hfix82_21_2 i) _)
      colCert_82_21_2.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T82_21
      hfix82_21 hinj82_21 hcardT82_21
      (fun i => conj_mem_of_fixedPoints _ _ (T82_21 i) (hfix82_21 i) _)
      ⟨82, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T82_21_2 Q2.hfix82_21_2 Q2.hinj82_21_2
      Q2.hcardT82_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_21_2 i) (Q2.hfix82_21_2 i) _)
      colCert_82_21_3.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T82_21
      hfix82_21 hinj82_21 hcardT82_21
      (fun i => conj_mem_of_fixedPoints _ _ (T82_21 i) (hfix82_21 i) _)
      ⟨82, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T82_21_2 Q2.hfix82_21_2 Q2.hinj82_21_2
      Q2.hcardT82_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_21_2 i) (Q2.hfix82_21_2 i) _)
      colCert_82_21_4.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T82_21
      hfix82_21 hinj82_21 hcardT82_21
      (fun i => conj_mem_of_fixedPoints _ _ (T82_21 i) (hfix82_21 i) _)
      ⟨82, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T82_21_2 Q2.hfix82_21_2 Q2.hinj82_21_2
      Q2.hcardT82_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_21_2 i) (Q2.hfix82_21_2 i) _)
      colCert_82_21_5.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T82_21
      hfix82_21 hinj82_21 hcardT82_21
      (fun i => conj_mem_of_fixedPoints _ _ (T82_21 i) (hfix82_21 i) _)
      ⟨82, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T82_21_2 Q2.hfix82_21_2 Q2.hinj82_21_2
      Q2.hcardT82_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_21_2 i) (Q2.hfix82_21_2 i) _)
      colCert_82_21_10.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T82_21
      hfix82_21 hinj82_21 hcardT82_21
      (fun i => conj_mem_of_fixedPoints _ _ (T82_21 i) (hfix82_21 i) _)
      ⟨82, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T82_21_2 Q2.hfix82_21_2 Q2.hinj82_21_2
      Q2.hcardT82_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_21_2 i) (Q2.hfix82_21_2 i) _)
      colCert_82_21_15.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T82_21
      hfix82_21 hinj82_21 hcardT82_21
      (fun i => conj_mem_of_fixedPoints _ _ (T82_21 i) (hfix82_21 i) _)
      ⟨82, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T82_21_2 Q2.hfix82_21_2 Q2.hinj82_21_2
      Q2.hcardT82_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_21_2 i) (Q2.hfix82_21_2 i) _)
      colCert_82_21_20.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T82_53
      hfix82_53 hinj82_53 hcardT82_53
      (fun i => conj_mem_of_fixedPoints _ _ (T82_53 i) (hfix82_53 i) _)
      ⟨82, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T82_53_2 Q2.hfix82_53_2 Q2.hinj82_53_2
      Q2.hcardT82_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_53_2 i) (Q2.hfix82_53_2 i) _)
      colCert_82_53_0.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T82_53
      hfix82_53 hinj82_53 hcardT82_53
      (fun i => conj_mem_of_fixedPoints _ _ (T82_53 i) (hfix82_53 i) _)
      ⟨82, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T82_53_2 Q2.hfix82_53_2 Q2.hinj82_53_2
      Q2.hcardT82_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_53_2 i) (Q2.hfix82_53_2 i) _)
      colCert_82_53_1.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T82_53
      hfix82_53 hinj82_53 hcardT82_53
      (fun i => conj_mem_of_fixedPoints _ _ (T82_53 i) (hfix82_53 i) _)
      ⟨82, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T82_53_2 Q2.hfix82_53_2 Q2.hinj82_53_2
      Q2.hcardT82_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_53_2 i) (Q2.hfix82_53_2 i) _)
      colCert_82_53_2.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T82_53
      hfix82_53 hinj82_53 hcardT82_53
      (fun i => conj_mem_of_fixedPoints _ _ (T82_53 i) (hfix82_53 i) _)
      ⟨82, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T82_53_2 Q2.hfix82_53_2 Q2.hinj82_53_2
      Q2.hcardT82_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_53_2 i) (Q2.hfix82_53_2 i) _)
      colCert_82_53_3.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T82_53
      hfix82_53 hinj82_53 hcardT82_53
      (fun i => conj_mem_of_fixedPoints _ _ (T82_53 i) (hfix82_53 i) _)
      ⟨82, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T82_53_2 Q2.hfix82_53_2 Q2.hinj82_53_2
      Q2.hcardT82_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_53_2 i) (Q2.hfix82_53_2 i) _)
      colCert_82_53_4.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T82_53
      hfix82_53 hinj82_53 hcardT82_53
      (fun i => conj_mem_of_fixedPoints _ _ (T82_53 i) (hfix82_53 i) _)
      ⟨82, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T82_53_2 Q2.hfix82_53_2 Q2.hinj82_53_2
      Q2.hcardT82_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_53_2 i) (Q2.hfix82_53_2 i) _)
      colCert_82_53_5.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T82_53
      hfix82_53 hinj82_53 hcardT82_53
      (fun i => conj_mem_of_fixedPoints _ _ (T82_53 i) (hfix82_53 i) _)
      ⟨82, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T82_53_2 Q2.hfix82_53_2 Q2.hinj82_53_2
      Q2.hcardT82_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_53_2 i) (Q2.hfix82_53_2 i) _)
      colCert_82_53_10.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T82_53
      hfix82_53 hinj82_53 hcardT82_53
      (fun i => conj_mem_of_fixedPoints _ _ (T82_53 i) (hfix82_53 i) _)
      ⟨82, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T82_53_2 Q2.hfix82_53_2 Q2.hinj82_53_2
      Q2.hcardT82_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_53_2 i) (Q2.hfix82_53_2 i) _)
      colCert_82_53_15.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T82_53
      hfix82_53 hinj82_53 hcardT82_53
      (fun i => conj_mem_of_fixedPoints _ _ (T82_53 i) (hfix82_53 i) _)
      ⟨82, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T82_53_2 Q2.hfix82_53_2 Q2.hinj82_53_2
      Q2.hcardT82_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_53_2 i) (Q2.hfix82_53_2 i) _)
      colCert_82_53_20.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_82_0 (hp : 0 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 0 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp)) T82_82
      hfix82_82 hinj82_82 hcardT82_82
      (fun i => conj_mem_of_fixedPoints _ _ (T82_82 i) (hfix82_82 i) _)
      ⟨82, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 0 hp) Q2.T82_82_2 Q2.hfix82_82_2 Q2.hinj82_82_2
      Q2.hcardT82_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_82_2 i) (Q2.hfix82_82_2 i) _)
      colCert_82_82_0.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_82_1 (hp : 1 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 1 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp)) T82_82
      hfix82_82 hinj82_82 hcardT82_82
      (fun i => conj_mem_of_fixedPoints _ _ (T82_82 i) (hfix82_82 i) _)
      ⟨82, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 1 hp) Q2.T82_82_2 Q2.hfix82_82_2 Q2.hinj82_82_2
      Q2.hcardT82_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_82_2 i) (Q2.hfix82_82_2 i) _)
      colCert_82_82_1.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_82_2 (hp : 2 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 2 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp)) T82_82
      hfix82_82 hinj82_82 hcardT82_82
      (fun i => conj_mem_of_fixedPoints _ _ (T82_82 i) (hfix82_82 i) _)
      ⟨82, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 2 hp) Q2.T82_82_2 Q2.hfix82_82_2 Q2.hinj82_82_2
      Q2.hcardT82_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_82_2 i) (Q2.hfix82_82_2 i) _)
      colCert_82_82_2.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_82_3 (hp : 3 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 3 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp)) T82_82
      hfix82_82 hinj82_82 hcardT82_82
      (fun i => conj_mem_of_fixedPoints _ _ (T82_82 i) (hfix82_82 i) _)
      ⟨82, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 3 hp) Q2.T82_82_2 Q2.hfix82_82_2 Q2.hinj82_82_2
      Q2.hcardT82_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_82_2 i) (Q2.hfix82_82_2 i) _)
      colCert_82_82_3.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_82_4 (hp : 4 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 4 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp)) T82_82
      hfix82_82 hinj82_82 hcardT82_82
      (fun i => conj_mem_of_fixedPoints _ _ (T82_82 i) (hfix82_82 i) _)
      ⟨82, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 4 hp) Q2.T82_82_2 Q2.hfix82_82_2 Q2.hinj82_82_2
      Q2.hcardT82_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_82_2 i) (Q2.hfix82_82_2 i) _)
      colCert_82_82_4.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_82_5 (hp : 5 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 5 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp)) T82_82
      hfix82_82 hinj82_82 hcardT82_82
      (fun i => conj_mem_of_fixedPoints _ _ (T82_82 i) (hfix82_82 i) _)
      ⟨82, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 5 hp) Q2.T82_82_2 Q2.hfix82_82_2 Q2.hinj82_82_2
      Q2.hcardT82_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_82_2 i) (Q2.hfix82_82_2 i) _)
      colCert_82_82_5.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_82_10 (hp : 10 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 10 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp)) T82_82
      hfix82_82 hinj82_82 hcardT82_82
      (fun i => conj_mem_of_fixedPoints _ _ (T82_82 i) (hfix82_82 i) _)
      ⟨82, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 10 hp) Q2.T82_82_2 Q2.hfix82_82_2 Q2.hinj82_82_2
      Q2.hcardT82_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_82_2 i) (Q2.hfix82_82_2 i) _)
      colCert_82_82_10.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_82_15 (hp : 15 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 15 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp)) T82_82
      hfix82_82 hinj82_82 hcardT82_82
      (fun i => conj_mem_of_fixedPoints _ _ (T82_82 i) (hfix82_82 i) _)
      ⟨82, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 15 hp) Q2.T82_82_2 Q2.hfix82_82_2 Q2.hinj82_82_2
      Q2.hcardT82_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_82_2 i) (Q2.hfix82_82_2 i) _)
      colCert_82_82_15.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_82_82_20 (hp : 20 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 82 []).length)
    (hq : (normIsRep.getD 82 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 20 hp)
        (rowE2 (⟨82, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp))
        (rowE1 (⟨82, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨82, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨82, by decide⟩ (listedAt ⟨82, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp)) T82_82
      hfix82_82 hinj82_82 hcardT82_82
      (fun i => conj_mem_of_fixedPoints _ _ (T82_82 i) (hfix82_82 i) _)
      ⟨82, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨82, by decide⟩ (Q2.listedAt ⟨82, by decide⟩
        (alnCheck_rep ⟨82, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 20 hp) Q2.T82_82_2 Q2.hfix82_82_2 Q2.hinj82_82_2
      Q2.hcardT82_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T82_82_2 i) (Q2.hfix82_82_2 i) _)
      colCert_82_82_20.hD ?_).symm
  rw [alnId_82 j hj]


theorem leaf_83_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T83_4
      hfix83_4 hinj83_4 hcardT83_4
      (fun i => conj_mem_of_fixedPoints _ _ (T83_4 i) (hfix83_4 i) _)
      ⟨83, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T83_4_2 Q2.hfix83_4_2 Q2.hinj83_4_2
      Q2.hcardT83_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_4_2 i) (Q2.hfix83_4_2 i) _)
      colCert_83_4_0.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T83_4
      hfix83_4 hinj83_4 hcardT83_4
      (fun i => conj_mem_of_fixedPoints _ _ (T83_4 i) (hfix83_4 i) _)
      ⟨83, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T83_4_2 Q2.hfix83_4_2 Q2.hinj83_4_2
      Q2.hcardT83_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_4_2 i) (Q2.hfix83_4_2 i) _)
      colCert_83_4_1.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T83_4
      hfix83_4 hinj83_4 hcardT83_4
      (fun i => conj_mem_of_fixedPoints _ _ (T83_4 i) (hfix83_4 i) _)
      ⟨83, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T83_4_2 Q2.hfix83_4_2 Q2.hinj83_4_2
      Q2.hcardT83_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_4_2 i) (Q2.hfix83_4_2 i) _)
      colCert_83_4_2.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T83_4
      hfix83_4 hinj83_4 hcardT83_4
      (fun i => conj_mem_of_fixedPoints _ _ (T83_4 i) (hfix83_4 i) _)
      ⟨83, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T83_4_2 Q2.hfix83_4_2 Q2.hinj83_4_2
      Q2.hcardT83_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_4_2 i) (Q2.hfix83_4_2 i) _)
      colCert_83_4_3.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T83_4
      hfix83_4 hinj83_4 hcardT83_4
      (fun i => conj_mem_of_fixedPoints _ _ (T83_4 i) (hfix83_4 i) _)
      ⟨83, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T83_4_2 Q2.hfix83_4_2 Q2.hinj83_4_2
      Q2.hcardT83_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_4_2 i) (Q2.hfix83_4_2 i) _)
      colCert_83_4_4.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T83_10
      hfix83_10 hinj83_10 hcardT83_10
      (fun i => conj_mem_of_fixedPoints _ _ (T83_10 i) (hfix83_10 i) _)
      ⟨83, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T83_10_2 Q2.hfix83_10_2 Q2.hinj83_10_2
      Q2.hcardT83_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_10_2 i) (Q2.hfix83_10_2 i) _)
      colCert_83_10_0.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T83_10
      hfix83_10 hinj83_10 hcardT83_10
      (fun i => conj_mem_of_fixedPoints _ _ (T83_10 i) (hfix83_10 i) _)
      ⟨83, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T83_10_2 Q2.hfix83_10_2 Q2.hinj83_10_2
      Q2.hcardT83_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_10_2 i) (Q2.hfix83_10_2 i) _)
      colCert_83_10_1.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T83_10
      hfix83_10 hinj83_10 hcardT83_10
      (fun i => conj_mem_of_fixedPoints _ _ (T83_10 i) (hfix83_10 i) _)
      ⟨83, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T83_10_2 Q2.hfix83_10_2 Q2.hinj83_10_2
      Q2.hcardT83_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_10_2 i) (Q2.hfix83_10_2 i) _)
      colCert_83_10_2.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T83_10
      hfix83_10 hinj83_10 hcardT83_10
      (fun i => conj_mem_of_fixedPoints _ _ (T83_10 i) (hfix83_10 i) _)
      ⟨83, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T83_10_2 Q2.hfix83_10_2 Q2.hinj83_10_2
      Q2.hcardT83_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_10_2 i) (Q2.hfix83_10_2 i) _)
      colCert_83_10_3.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T83_10
      hfix83_10 hinj83_10 hcardT83_10
      (fun i => conj_mem_of_fixedPoints _ _ (T83_10 i) (hfix83_10 i) _)
      ⟨83, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T83_10_2 Q2.hfix83_10_2 Q2.hinj83_10_2
      Q2.hcardT83_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_10_2 i) (Q2.hfix83_10_2 i) _)
      colCert_83_10_4.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T83_12
      hfix83_12 hinj83_12 hcardT83_12
      (fun i => conj_mem_of_fixedPoints _ _ (T83_12 i) (hfix83_12 i) _)
      ⟨83, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T83_12_2 Q2.hfix83_12_2 Q2.hinj83_12_2
      Q2.hcardT83_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_12_2 i) (Q2.hfix83_12_2 i) _)
      colCert_83_12_0.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T83_12
      hfix83_12 hinj83_12 hcardT83_12
      (fun i => conj_mem_of_fixedPoints _ _ (T83_12 i) (hfix83_12 i) _)
      ⟨83, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T83_12_2 Q2.hfix83_12_2 Q2.hinj83_12_2
      Q2.hcardT83_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_12_2 i) (Q2.hfix83_12_2 i) _)
      colCert_83_12_1.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T83_12
      hfix83_12 hinj83_12 hcardT83_12
      (fun i => conj_mem_of_fixedPoints _ _ (T83_12 i) (hfix83_12 i) _)
      ⟨83, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T83_12_2 Q2.hfix83_12_2 Q2.hinj83_12_2
      Q2.hcardT83_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_12_2 i) (Q2.hfix83_12_2 i) _)
      colCert_83_12_2.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T83_12
      hfix83_12 hinj83_12 hcardT83_12
      (fun i => conj_mem_of_fixedPoints _ _ (T83_12 i) (hfix83_12 i) _)
      ⟨83, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T83_12_2 Q2.hfix83_12_2 Q2.hinj83_12_2
      Q2.hcardT83_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_12_2 i) (Q2.hfix83_12_2 i) _)
      colCert_83_12_3.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T83_12
      hfix83_12 hinj83_12 hcardT83_12
      (fun i => conj_mem_of_fixedPoints _ _ (T83_12 i) (hfix83_12 i) _)
      ⟨83, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T83_12_2 Q2.hfix83_12_2 Q2.hinj83_12_2
      Q2.hcardT83_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_12_2 i) (Q2.hfix83_12_2 i) _)
      colCert_83_12_4.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T83_22
      hfix83_22 hinj83_22 hcardT83_22
      (fun i => conj_mem_of_fixedPoints _ _ (T83_22 i) (hfix83_22 i) _)
      ⟨83, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T83_22_2 Q2.hfix83_22_2 Q2.hinj83_22_2
      Q2.hcardT83_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_22_2 i) (Q2.hfix83_22_2 i) _)
      colCert_83_22_0.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T83_22
      hfix83_22 hinj83_22 hcardT83_22
      (fun i => conj_mem_of_fixedPoints _ _ (T83_22 i) (hfix83_22 i) _)
      ⟨83, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T83_22_2 Q2.hfix83_22_2 Q2.hinj83_22_2
      Q2.hcardT83_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_22_2 i) (Q2.hfix83_22_2 i) _)
      colCert_83_22_1.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T83_22
      hfix83_22 hinj83_22 hcardT83_22
      (fun i => conj_mem_of_fixedPoints _ _ (T83_22 i) (hfix83_22 i) _)
      ⟨83, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T83_22_2 Q2.hfix83_22_2 Q2.hinj83_22_2
      Q2.hcardT83_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_22_2 i) (Q2.hfix83_22_2 i) _)
      colCert_83_22_2.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T83_22
      hfix83_22 hinj83_22 hcardT83_22
      (fun i => conj_mem_of_fixedPoints _ _ (T83_22 i) (hfix83_22 i) _)
      ⟨83, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T83_22_2 Q2.hfix83_22_2 Q2.hinj83_22_2
      Q2.hcardT83_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_22_2 i) (Q2.hfix83_22_2 i) _)
      colCert_83_22_3.hD ?_).symm
  rw [alnId_83 j hj]


end LeanDring.P5Presentation
