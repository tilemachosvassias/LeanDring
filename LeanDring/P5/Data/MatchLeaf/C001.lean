/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SpeciesTable.Twin1.ColDataGap
import LeanDring.P5.Data.ColRestCheap.C001
import LeanDring.P5.Data.ColRestCheap.C138
import LeanDring.P5.Data.ColRestCheap.C139
import LeanDring.P5.Data.ColRestCheap.C018
import LeanDring.P5.Data.ColRestHeavy.C038
import LeanDring.P5.Data.ColRestHeavy.C039
import LeanDring.P5.Data.ColRestHeavy.C040
import LeanDring.P5.Data.ColRestHeavy.C041
import LeanDring.P5.Data.ColRestHeavy.C042
import LeanDring.P5.Data.ColRestHeavy.C043
import LeanDring.P5.Data.ColTau.C001
import LeanDring.P5.Data.EntryA.C001
import LeanDring.P5.Data.EntryA.C004
import LeanDring.P5.Certificate.SpeciesTable.Twin2.EntryDataGap
import LeanDring.P5.Data.EntryK.C002
import LeanDring.P5.Data.EntryK.C011
import LeanDring.P5.Data.EntryK.C012
import LeanDring.P5.Data.EntryK.C013
import LeanDring.P5.Data.EntryK.C003
import LeanDring.P5.Data.EntryK.C004
import LeanDring.P5.Data.EntryK.C005
import LeanDring.P5.Data.EntryK.C006
import LeanDring.P5.Data.EntryK.C007
import LeanDring.P5.Data.EntryK.C008
import LeanDring.P5.Data.EntryK.C009
import LeanDring.P5.Data.EntryK.C010
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk01

/-! # Stage-5 leaves, chunk 0 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_1_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 1 []).length)
    (hq : (normIsRep.getD 1 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨1, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨1, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨1, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨1, by decide⟩ (listedAt ⟨1, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T1_1
      hfix1_1 hinj1_1 hcardT1_1
      (fun i => conj_mem_of_fixedPoints _ _ (T1_1 i) (hfix1_1 i) _)
      ⟨1, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨1, by decide⟩ (Q2.listedAt ⟨1, by decide⟩
        (alnCheck_rep ⟨1, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T1_1_2 Q2.hfix1_1_2 Q2.hinj1_1_2
      Q2.hcardT1_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T1_1_2 i) (Q2.hfix1_1_2 i) _)
      colCert_1_1_0.hD ?_).symm
  rw [alnId_1 j hj]


theorem leaf_1_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 1 []).length)
    (hq : (normIsRep.getD 1 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨1, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨1, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨1, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨1, by decide⟩ (listedAt ⟨1, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T1_1
      hfix1_1 hinj1_1 hcardT1_1
      (fun i => conj_mem_of_fixedPoints _ _ (T1_1 i) (hfix1_1 i) _)
      ⟨1, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨1, by decide⟩ (Q2.listedAt ⟨1, by decide⟩
        (alnCheck_rep ⟨1, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T1_1_2 Q2.hfix1_1_2 Q2.hinj1_1_2
      Q2.hcardT1_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T1_1_2 i) (Q2.hfix1_1_2 i) _)
      colCert_1_1_1.hD ?_).symm
  rw [alnId_1 j hj]


theorem leaf_1_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 1 []).length)
    (hq : (normIsRep.getD 1 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨1, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨1, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨1, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨1, by decide⟩ (listedAt ⟨1, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T1_1
      hfix1_1 hinj1_1 hcardT1_1
      (fun i => conj_mem_of_fixedPoints _ _ (T1_1 i) (hfix1_1 i) _)
      ⟨1, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨1, by decide⟩ (Q2.listedAt ⟨1, by decide⟩
        (alnCheck_rep ⟨1, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T1_1_2 Q2.hfix1_1_2 Q2.hinj1_1_2
      Q2.hcardT1_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T1_1_2 i) (Q2.hfix1_1_2 i) _)
      colCert_1_1_2.hD ?_).symm
  rw [alnId_1 j hj]


theorem leaf_1_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 1 []).length)
    (hq : (normIsRep.getD 1 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨1, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨1, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨1, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨1, by decide⟩ (listedAt ⟨1, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T1_1
      hfix1_1 hinj1_1 hcardT1_1
      (fun i => conj_mem_of_fixedPoints _ _ (T1_1 i) (hfix1_1 i) _)
      ⟨1, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨1, by decide⟩ (Q2.listedAt ⟨1, by decide⟩
        (alnCheck_rep ⟨1, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T1_1_2 Q2.hfix1_1_2 Q2.hinj1_1_2
      Q2.hcardT1_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T1_1_2 i) (Q2.hfix1_1_2 i) _)
      colCert_1_1_3.hD ?_).symm
  rw [alnId_1 j hj]


theorem leaf_1_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 1 []).length)
    (hq : (normIsRep.getD 1 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨1, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨1, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨1, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨1, by decide⟩ (listedAt ⟨1, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T1_1
      hfix1_1 hinj1_1 hcardT1_1
      (fun i => conj_mem_of_fixedPoints _ _ (T1_1 i) (hfix1_1 i) _)
      ⟨1, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨1, by decide⟩ (Q2.listedAt ⟨1, by decide⟩
        (alnCheck_rep ⟨1, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T1_1_2 Q2.hfix1_1_2 Q2.hinj1_1_2
      Q2.hcardT1_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T1_1_2 i) (Q2.hfix1_1_2 i) _)
      colCert_1_1_4.hD ?_).symm
  rw [alnId_1 j hj]


theorem leaf_2_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 2 []).length)
    (hq : (normIsRep.getD 2 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨2, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨2, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨2, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨2, by decide⟩ (listedAt ⟨2, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T2_2
      hfix2_2 hinj2_2 hcardT2_2
      (fun i => conj_mem_of_fixedPoints _ _ (T2_2 i) (hfix2_2 i) _)
      ⟨2, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨2, by decide⟩ (Q2.listedAt ⟨2, by decide⟩
        (alnCheck_rep ⟨2, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T2_2_2 Q2.hfix2_2_2 Q2.hinj2_2_2
      Q2.hcardT2_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T2_2_2 i) (Q2.hfix2_2_2 i) _)
      colCert_2_2_0.hD ?_).symm
  rw [alnId_2 j hj]


theorem leaf_2_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 2 []).length)
    (hq : (normIsRep.getD 2 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨2, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨2, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨2, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨2, by decide⟩ (listedAt ⟨2, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T2_2
      hfix2_2 hinj2_2 hcardT2_2
      (fun i => conj_mem_of_fixedPoints _ _ (T2_2 i) (hfix2_2 i) _)
      ⟨2, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨2, by decide⟩ (Q2.listedAt ⟨2, by decide⟩
        (alnCheck_rep ⟨2, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T2_2_2 Q2.hfix2_2_2 Q2.hinj2_2_2
      Q2.hcardT2_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T2_2_2 i) (Q2.hfix2_2_2 i) _)
      colCert_2_2_1.hD ?_).symm
  rw [alnId_2 j hj]


theorem leaf_2_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 2 []).length)
    (hq : (normIsRep.getD 2 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨2, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨2, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨2, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨2, by decide⟩ (listedAt ⟨2, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T2_2
      hfix2_2 hinj2_2 hcardT2_2
      (fun i => conj_mem_of_fixedPoints _ _ (T2_2 i) (hfix2_2 i) _)
      ⟨2, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨2, by decide⟩ (Q2.listedAt ⟨2, by decide⟩
        (alnCheck_rep ⟨2, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T2_2_2 Q2.hfix2_2_2 Q2.hinj2_2_2
      Q2.hcardT2_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T2_2_2 i) (Q2.hfix2_2_2 i) _)
      colCert_2_2_2.hD ?_).symm
  rw [alnId_2 j hj]


theorem leaf_2_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 2 []).length)
    (hq : (normIsRep.getD 2 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨2, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨2, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨2, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨2, by decide⟩ (listedAt ⟨2, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T2_2
      hfix2_2 hinj2_2 hcardT2_2
      (fun i => conj_mem_of_fixedPoints _ _ (T2_2 i) (hfix2_2 i) _)
      ⟨2, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨2, by decide⟩ (Q2.listedAt ⟨2, by decide⟩
        (alnCheck_rep ⟨2, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T2_2_2 Q2.hfix2_2_2 Q2.hinj2_2_2
      Q2.hcardT2_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T2_2_2 i) (Q2.hfix2_2_2 i) _)
      colCert_2_2_3.hD ?_).symm
  rw [alnId_2 j hj]


theorem leaf_2_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 2 []).length)
    (hq : (normIsRep.getD 2 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨2, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨2, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨2, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨2, by decide⟩ (listedAt ⟨2, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T2_2
      hfix2_2 hinj2_2 hcardT2_2
      (fun i => conj_mem_of_fixedPoints _ _ (T2_2 i) (hfix2_2 i) _)
      ⟨2, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨2, by decide⟩ (Q2.listedAt ⟨2, by decide⟩
        (alnCheck_rep ⟨2, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T2_2_2 Q2.hfix2_2_2 Q2.hinj2_2_2
      Q2.hcardT2_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T2_2_2 i) (Q2.hfix2_2_2 i) _)
      colCert_2_2_4.hD ?_).symm
  rw [alnId_2 j hj]


theorem leaf_3_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 3 []).length)
    (hq : (normIsRep.getD 3 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨3, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨3, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨3, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨3, by decide⟩ (listedAt ⟨3, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T3_3
      hfix3_3 hinj3_3 hcardT3_3
      (fun i => conj_mem_of_fixedPoints _ _ (T3_3 i) (hfix3_3 i) _)
      ⟨3, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨3, by decide⟩ (Q2.listedAt ⟨3, by decide⟩
        (alnCheck_rep ⟨3, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T3_3_2 Q2.hfix3_3_2 Q2.hinj3_3_2
      Q2.hcardT3_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T3_3_2 i) (Q2.hfix3_3_2 i) _)
      colCert_3_3_0.hD ?_).symm
  rw [alnId_3 j hj]


theorem leaf_3_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 3 []).length)
    (hq : (normIsRep.getD 3 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨3, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨3, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨3, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨3, by decide⟩ (listedAt ⟨3, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T3_3
      hfix3_3 hinj3_3 hcardT3_3
      (fun i => conj_mem_of_fixedPoints _ _ (T3_3 i) (hfix3_3 i) _)
      ⟨3, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨3, by decide⟩ (Q2.listedAt ⟨3, by decide⟩
        (alnCheck_rep ⟨3, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T3_3_2 Q2.hfix3_3_2 Q2.hinj3_3_2
      Q2.hcardT3_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T3_3_2 i) (Q2.hfix3_3_2 i) _)
      colCert_3_3_1.hD ?_).symm
  rw [alnId_3 j hj]


theorem leaf_3_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 3 []).length)
    (hq : (normIsRep.getD 3 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨3, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨3, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨3, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨3, by decide⟩ (listedAt ⟨3, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T3_3
      hfix3_3 hinj3_3 hcardT3_3
      (fun i => conj_mem_of_fixedPoints _ _ (T3_3 i) (hfix3_3 i) _)
      ⟨3, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨3, by decide⟩ (Q2.listedAt ⟨3, by decide⟩
        (alnCheck_rep ⟨3, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T3_3_2 Q2.hfix3_3_2 Q2.hinj3_3_2
      Q2.hcardT3_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T3_3_2 i) (Q2.hfix3_3_2 i) _)
      colCert_3_3_2.hD ?_).symm
  rw [alnId_3 j hj]


theorem leaf_3_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 3 []).length)
    (hq : (normIsRep.getD 3 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨3, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨3, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨3, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨3, by decide⟩ (listedAt ⟨3, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T3_3
      hfix3_3 hinj3_3 hcardT3_3
      (fun i => conj_mem_of_fixedPoints _ _ (T3_3 i) (hfix3_3 i) _)
      ⟨3, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨3, by decide⟩ (Q2.listedAt ⟨3, by decide⟩
        (alnCheck_rep ⟨3, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T3_3_2 Q2.hfix3_3_2 Q2.hinj3_3_2
      Q2.hcardT3_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T3_3_2 i) (Q2.hfix3_3_2 i) _)
      colCert_3_3_3.hD ?_).symm
  rw [alnId_3 j hj]


theorem leaf_3_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 3 []).length)
    (hq : (normIsRep.getD 3 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨3, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨3, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨3, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨3, by decide⟩ (listedAt ⟨3, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T3_3
      hfix3_3 hinj3_3 hcardT3_3
      (fun i => conj_mem_of_fixedPoints _ _ (T3_3 i) (hfix3_3 i) _)
      ⟨3, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨3, by decide⟩ (Q2.listedAt ⟨3, by decide⟩
        (alnCheck_rep ⟨3, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T3_3_2 Q2.hfix3_3_2 Q2.hinj3_3_2
      Q2.hcardT3_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T3_3_2 i) (Q2.hfix3_3_2 i) _)
      colCert_3_3_4.hD ?_).symm
  rw [alnId_3 j hj]


theorem leaf_4_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 4 []).length)
    (hq : (normIsRep.getD 4 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨4, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨4, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨4, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨4, by decide⟩ (listedAt ⟨4, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T4_4
      hfix4_4 hinj4_4 hcardT4_4
      (fun i => conj_mem_of_fixedPoints _ _ (T4_4 i) (hfix4_4 i) _)
      ⟨4, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨4, by decide⟩ (Q2.listedAt ⟨4, by decide⟩
        (alnCheck_rep ⟨4, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T4_4_2 Q2.hfix4_4_2 Q2.hinj4_4_2
      Q2.hcardT4_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T4_4_2 i) (Q2.hfix4_4_2 i) _)
      colCert_4_4_0.hD ?_).symm
  rw [alnId_4 j hj]


theorem leaf_4_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 4 []).length)
    (hq : (normIsRep.getD 4 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨4, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨4, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨4, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨4, by decide⟩ (listedAt ⟨4, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T4_4
      hfix4_4 hinj4_4 hcardT4_4
      (fun i => conj_mem_of_fixedPoints _ _ (T4_4 i) (hfix4_4 i) _)
      ⟨4, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨4, by decide⟩ (Q2.listedAt ⟨4, by decide⟩
        (alnCheck_rep ⟨4, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T4_4_2 Q2.hfix4_4_2 Q2.hinj4_4_2
      Q2.hcardT4_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T4_4_2 i) (Q2.hfix4_4_2 i) _)
      colCert_4_4_1.hD ?_).symm
  rw [alnId_4 j hj]


theorem leaf_4_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 4 []).length)
    (hq : (normIsRep.getD 4 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨4, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨4, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨4, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨4, by decide⟩ (listedAt ⟨4, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T4_4
      hfix4_4 hinj4_4 hcardT4_4
      (fun i => conj_mem_of_fixedPoints _ _ (T4_4 i) (hfix4_4 i) _)
      ⟨4, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨4, by decide⟩ (Q2.listedAt ⟨4, by decide⟩
        (alnCheck_rep ⟨4, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T4_4_2 Q2.hfix4_4_2 Q2.hinj4_4_2
      Q2.hcardT4_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T4_4_2 i) (Q2.hfix4_4_2 i) _)
      colCert_4_4_2.hD ?_).symm
  rw [alnId_4 j hj]


theorem leaf_4_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 4 []).length)
    (hq : (normIsRep.getD 4 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨4, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨4, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨4, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨4, by decide⟩ (listedAt ⟨4, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T4_4
      hfix4_4 hinj4_4 hcardT4_4
      (fun i => conj_mem_of_fixedPoints _ _ (T4_4 i) (hfix4_4 i) _)
      ⟨4, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨4, by decide⟩ (Q2.listedAt ⟨4, by decide⟩
        (alnCheck_rep ⟨4, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T4_4_2 Q2.hfix4_4_2 Q2.hinj4_4_2
      Q2.hcardT4_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T4_4_2 i) (Q2.hfix4_4_2 i) _)
      colCert_4_4_3.hD ?_).symm
  rw [alnId_4 j hj]


theorem leaf_4_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 4 []).length)
    (hq : (normIsRep.getD 4 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨4, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨4, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨4, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨4, by decide⟩ (listedAt ⟨4, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T4_4
      hfix4_4 hinj4_4 hcardT4_4
      (fun i => conj_mem_of_fixedPoints _ _ (T4_4 i) (hfix4_4 i) _)
      ⟨4, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨4, by decide⟩ (Q2.listedAt ⟨4, by decide⟩
        (alnCheck_rep ⟨4, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T4_4_2 Q2.hfix4_4_2 Q2.hinj4_4_2
      Q2.hcardT4_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T4_4_2 i) (Q2.hfix4_4_2 i) _)
      colCert_4_4_4.hD ?_).symm
  rw [alnId_4 j hj]


theorem leaf_5_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 5 []).length)
    (hq : (normIsRep.getD 5 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨5, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨5, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨5, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨5, by decide⟩ (listedAt ⟨5, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T5_5
      hfix5_5 hinj5_5 hcardT5_5
      (fun i => conj_mem_of_fixedPoints _ _ (T5_5 i) (hfix5_5 i) _)
      ⟨5, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨5, by decide⟩ (Q2.listedAt ⟨5, by decide⟩
        (alnCheck_rep ⟨5, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T5_5_2 Q2.hfix5_5_2 Q2.hinj5_5_2
      Q2.hcardT5_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T5_5_2 i) (Q2.hfix5_5_2 i) _)
      colCert_5_5_0.hD ?_).symm
  rw [alnId_5 j hj]


theorem leaf_5_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 5 []).length)
    (hq : (normIsRep.getD 5 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨5, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨5, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨5, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨5, by decide⟩ (listedAt ⟨5, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T5_5
      hfix5_5 hinj5_5 hcardT5_5
      (fun i => conj_mem_of_fixedPoints _ _ (T5_5 i) (hfix5_5 i) _)
      ⟨5, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨5, by decide⟩ (Q2.listedAt ⟨5, by decide⟩
        (alnCheck_rep ⟨5, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T5_5_2 Q2.hfix5_5_2 Q2.hinj5_5_2
      Q2.hcardT5_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T5_5_2 i) (Q2.hfix5_5_2 i) _)
      colCert_5_5_1.hD ?_).symm
  rw [alnId_5 j hj]


theorem leaf_5_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 5 []).length)
    (hq : (normIsRep.getD 5 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨5, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨5, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨5, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨5, by decide⟩ (listedAt ⟨5, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T5_5
      hfix5_5 hinj5_5 hcardT5_5
      (fun i => conj_mem_of_fixedPoints _ _ (T5_5 i) (hfix5_5 i) _)
      ⟨5, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨5, by decide⟩ (Q2.listedAt ⟨5, by decide⟩
        (alnCheck_rep ⟨5, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T5_5_2 Q2.hfix5_5_2 Q2.hinj5_5_2
      Q2.hcardT5_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T5_5_2 i) (Q2.hfix5_5_2 i) _)
      colCert_5_5_2.hD ?_).symm
  rw [alnId_5 j hj]


theorem leaf_5_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 5 []).length)
    (hq : (normIsRep.getD 5 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨5, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨5, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨5, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨5, by decide⟩ (listedAt ⟨5, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T5_5
      hfix5_5 hinj5_5 hcardT5_5
      (fun i => conj_mem_of_fixedPoints _ _ (T5_5 i) (hfix5_5 i) _)
      ⟨5, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨5, by decide⟩ (Q2.listedAt ⟨5, by decide⟩
        (alnCheck_rep ⟨5, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T5_5_2 Q2.hfix5_5_2 Q2.hinj5_5_2
      Q2.hcardT5_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T5_5_2 i) (Q2.hfix5_5_2 i) _)
      colCert_5_5_3.hD ?_).symm
  rw [alnId_5 j hj]


theorem leaf_5_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 5 []).length)
    (hq : (normIsRep.getD 5 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨5, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨5, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨5, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨5, by decide⟩ (listedAt ⟨5, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T5_5
      hfix5_5 hinj5_5 hcardT5_5
      (fun i => conj_mem_of_fixedPoints _ _ (T5_5 i) (hfix5_5 i) _)
      ⟨5, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨5, by decide⟩ (Q2.listedAt ⟨5, by decide⟩
        (alnCheck_rep ⟨5, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T5_5_2 Q2.hfix5_5_2 Q2.hinj5_5_2
      Q2.hcardT5_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T5_5_2 i) (Q2.hfix5_5_2 i) _)
      colCert_5_5_4.hD ?_).symm
  rw [alnId_5 j hj]


theorem leaf_6_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 6 []).length)
    (hq : (normIsRep.getD 6 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨6, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨6, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨6, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨6, by decide⟩ (listedAt ⟨6, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T6_6
      hfix6_6 hinj6_6 hcardT6_6
      (fun i => conj_mem_of_fixedPoints _ _ (T6_6 i) (hfix6_6 i) _)
      ⟨6, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨6, by decide⟩ (Q2.listedAt ⟨6, by decide⟩
        (alnCheck_rep ⟨6, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T6_6_2 Q2.hfix6_6_2 Q2.hinj6_6_2
      Q2.hcardT6_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T6_6_2 i) (Q2.hfix6_6_2 i) _)
      colCert_6_6_0.hD ?_).symm
  rw [alnId_6 j hj]


theorem leaf_6_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 6 []).length)
    (hq : (normIsRep.getD 6 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨6, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨6, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨6, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨6, by decide⟩ (listedAt ⟨6, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T6_6
      hfix6_6 hinj6_6 hcardT6_6
      (fun i => conj_mem_of_fixedPoints _ _ (T6_6 i) (hfix6_6 i) _)
      ⟨6, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨6, by decide⟩ (Q2.listedAt ⟨6, by decide⟩
        (alnCheck_rep ⟨6, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T6_6_2 Q2.hfix6_6_2 Q2.hinj6_6_2
      Q2.hcardT6_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T6_6_2 i) (Q2.hfix6_6_2 i) _)
      colCert_6_6_1.hD ?_).symm
  rw [alnId_6 j hj]


theorem leaf_6_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 6 []).length)
    (hq : (normIsRep.getD 6 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨6, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨6, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨6, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨6, by decide⟩ (listedAt ⟨6, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T6_6
      hfix6_6 hinj6_6 hcardT6_6
      (fun i => conj_mem_of_fixedPoints _ _ (T6_6 i) (hfix6_6 i) _)
      ⟨6, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨6, by decide⟩ (Q2.listedAt ⟨6, by decide⟩
        (alnCheck_rep ⟨6, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T6_6_2 Q2.hfix6_6_2 Q2.hinj6_6_2
      Q2.hcardT6_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T6_6_2 i) (Q2.hfix6_6_2 i) _)
      colCert_6_6_2.hD ?_).symm
  rw [alnId_6 j hj]


theorem leaf_6_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 6 []).length)
    (hq : (normIsRep.getD 6 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨6, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨6, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨6, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨6, by decide⟩ (listedAt ⟨6, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T6_6
      hfix6_6 hinj6_6 hcardT6_6
      (fun i => conj_mem_of_fixedPoints _ _ (T6_6 i) (hfix6_6 i) _)
      ⟨6, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨6, by decide⟩ (Q2.listedAt ⟨6, by decide⟩
        (alnCheck_rep ⟨6, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T6_6_2 Q2.hfix6_6_2 Q2.hinj6_6_2
      Q2.hcardT6_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T6_6_2 i) (Q2.hfix6_6_2 i) _)
      colCert_6_6_3.hD ?_).symm
  rw [alnId_6 j hj]


theorem leaf_6_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 6 []).length)
    (hq : (normIsRep.getD 6 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨6, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨6, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨6, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨6, by decide⟩ (listedAt ⟨6, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T6_6
      hfix6_6 hinj6_6 hcardT6_6
      (fun i => conj_mem_of_fixedPoints _ _ (T6_6 i) (hfix6_6 i) _)
      ⟨6, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨6, by decide⟩ (Q2.listedAt ⟨6, by decide⟩
        (alnCheck_rep ⟨6, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T6_6_2 Q2.hfix6_6_2 Q2.hinj6_6_2
      Q2.hcardT6_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T6_6_2 i) (Q2.hfix6_6_2 i) _)
      colCert_6_6_4.hD ?_).symm
  rw [alnId_6 j hj]


theorem leaf_7_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 7 []).length)
    (hq : (normIsRep.getD 7 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨7, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨7, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨7, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨7, by decide⟩ (listedAt ⟨7, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T7_7
      hfix7_7 hinj7_7 hcardT7_7
      (fun i => conj_mem_of_fixedPoints _ _ (T7_7 i) (hfix7_7 i) _)
      ⟨7, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨7, by decide⟩ (Q2.listedAt ⟨7, by decide⟩
        (alnCheck_rep ⟨7, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T7_7_2 Q2.hfix7_7_2 Q2.hinj7_7_2
      Q2.hcardT7_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T7_7_2 i) (Q2.hfix7_7_2 i) _)
      colCert_7_7_0.hD ?_).symm
  rw [alnId_7 j hj]


theorem leaf_7_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 7 []).length)
    (hq : (normIsRep.getD 7 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨7, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨7, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨7, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨7, by decide⟩ (listedAt ⟨7, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T7_7
      hfix7_7 hinj7_7 hcardT7_7
      (fun i => conj_mem_of_fixedPoints _ _ (T7_7 i) (hfix7_7 i) _)
      ⟨7, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨7, by decide⟩ (Q2.listedAt ⟨7, by decide⟩
        (alnCheck_rep ⟨7, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T7_7_2 Q2.hfix7_7_2 Q2.hinj7_7_2
      Q2.hcardT7_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T7_7_2 i) (Q2.hfix7_7_2 i) _)
      colCert_7_7_1.hD ?_).symm
  rw [alnId_7 j hj]


theorem leaf_7_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 7 []).length)
    (hq : (normIsRep.getD 7 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨7, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨7, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨7, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨7, by decide⟩ (listedAt ⟨7, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T7_7
      hfix7_7 hinj7_7 hcardT7_7
      (fun i => conj_mem_of_fixedPoints _ _ (T7_7 i) (hfix7_7 i) _)
      ⟨7, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨7, by decide⟩ (Q2.listedAt ⟨7, by decide⟩
        (alnCheck_rep ⟨7, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T7_7_2 Q2.hfix7_7_2 Q2.hinj7_7_2
      Q2.hcardT7_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T7_7_2 i) (Q2.hfix7_7_2 i) _)
      colCert_7_7_2.hD ?_).symm
  rw [alnId_7 j hj]


theorem leaf_7_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 7 []).length)
    (hq : (normIsRep.getD 7 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨7, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨7, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨7, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨7, by decide⟩ (listedAt ⟨7, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T7_7
      hfix7_7 hinj7_7 hcardT7_7
      (fun i => conj_mem_of_fixedPoints _ _ (T7_7 i) (hfix7_7 i) _)
      ⟨7, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨7, by decide⟩ (Q2.listedAt ⟨7, by decide⟩
        (alnCheck_rep ⟨7, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T7_7_2 Q2.hfix7_7_2 Q2.hinj7_7_2
      Q2.hcardT7_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T7_7_2 i) (Q2.hfix7_7_2 i) _)
      colCert_7_7_3.hD ?_).symm
  rw [alnId_7 j hj]


theorem leaf_7_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 7 []).length)
    (hq : (normIsRep.getD 7 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨7, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨7, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨7, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨7, by decide⟩ (listedAt ⟨7, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T7_7
      hfix7_7 hinj7_7 hcardT7_7
      (fun i => conj_mem_of_fixedPoints _ _ (T7_7 i) (hfix7_7 i) _)
      ⟨7, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨7, by decide⟩ (Q2.listedAt ⟨7, by decide⟩
        (alnCheck_rep ⟨7, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T7_7_2 Q2.hfix7_7_2 Q2.hinj7_7_2
      Q2.hcardT7_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T7_7_2 i) (Q2.hfix7_7_2 i) _)
      colCert_7_7_4.hD ?_).symm
  rw [alnId_7 j hj]


theorem leaf_8_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 8 []).length)
    (hq : (normIsRep.getD 8 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨8, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨8, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨8, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨8, by decide⟩ (listedAt ⟨8, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T8_8
      hfix8_8 hinj8_8 hcardT8_8
      (fun i => conj_mem_of_fixedPoints _ _ (T8_8 i) (hfix8_8 i) _)
      ⟨8, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨8, by decide⟩ (Q2.listedAt ⟨8, by decide⟩
        (alnCheck_rep ⟨8, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T8_8_2 Q2.hfix8_8_2 Q2.hinj8_8_2
      Q2.hcardT8_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T8_8_2 i) (Q2.hfix8_8_2 i) _)
      colCert_8_8_0.hD ?_).symm
  rw [alnId_8 j hj]


theorem leaf_8_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 8 []).length)
    (hq : (normIsRep.getD 8 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨8, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨8, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨8, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨8, by decide⟩ (listedAt ⟨8, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T8_8
      hfix8_8 hinj8_8 hcardT8_8
      (fun i => conj_mem_of_fixedPoints _ _ (T8_8 i) (hfix8_8 i) _)
      ⟨8, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨8, by decide⟩ (Q2.listedAt ⟨8, by decide⟩
        (alnCheck_rep ⟨8, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T8_8_2 Q2.hfix8_8_2 Q2.hinj8_8_2
      Q2.hcardT8_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T8_8_2 i) (Q2.hfix8_8_2 i) _)
      colCert_8_8_1.hD ?_).symm
  rw [alnId_8 j hj]


theorem leaf_8_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 8 []).length)
    (hq : (normIsRep.getD 8 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨8, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨8, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨8, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨8, by decide⟩ (listedAt ⟨8, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T8_8
      hfix8_8 hinj8_8 hcardT8_8
      (fun i => conj_mem_of_fixedPoints _ _ (T8_8 i) (hfix8_8 i) _)
      ⟨8, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨8, by decide⟩ (Q2.listedAt ⟨8, by decide⟩
        (alnCheck_rep ⟨8, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T8_8_2 Q2.hfix8_8_2 Q2.hinj8_8_2
      Q2.hcardT8_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T8_8_2 i) (Q2.hfix8_8_2 i) _)
      colCert_8_8_2.hD ?_).symm
  rw [alnId_8 j hj]


theorem leaf_8_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 8 []).length)
    (hq : (normIsRep.getD 8 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨8, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨8, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨8, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨8, by decide⟩ (listedAt ⟨8, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T8_8
      hfix8_8 hinj8_8 hcardT8_8
      (fun i => conj_mem_of_fixedPoints _ _ (T8_8 i) (hfix8_8 i) _)
      ⟨8, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨8, by decide⟩ (Q2.listedAt ⟨8, by decide⟩
        (alnCheck_rep ⟨8, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T8_8_2 Q2.hfix8_8_2 Q2.hinj8_8_2
      Q2.hcardT8_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T8_8_2 i) (Q2.hfix8_8_2 i) _)
      colCert_8_8_3.hD ?_).symm
  rw [alnId_8 j hj]


theorem leaf_8_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 8 []).length)
    (hq : (normIsRep.getD 8 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨8, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨8, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨8, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨8, by decide⟩ (listedAt ⟨8, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T8_8
      hfix8_8 hinj8_8 hcardT8_8
      (fun i => conj_mem_of_fixedPoints _ _ (T8_8 i) (hfix8_8 i) _)
      ⟨8, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨8, by decide⟩ (Q2.listedAt ⟨8, by decide⟩
        (alnCheck_rep ⟨8, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T8_8_2 Q2.hfix8_8_2 Q2.hinj8_8_2
      Q2.hcardT8_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T8_8_2 i) (Q2.hfix8_8_2 i) _)
      colCert_8_8_4.hD ?_).symm
  rw [alnId_8 j hj]


theorem leaf_9_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 9 []).length)
    (hq : (normIsRep.getD 9 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨9, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨9, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨9, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨9, by decide⟩ (listedAt ⟨9, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T9_9
      hfix9_9 hinj9_9 hcardT9_9
      (fun i => conj_mem_of_fixedPoints _ _ (T9_9 i) (hfix9_9 i) _)
      ⟨9, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨9, by decide⟩ (Q2.listedAt ⟨9, by decide⟩
        (alnCheck_rep ⟨9, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T9_9_2 Q2.hfix9_9_2 Q2.hinj9_9_2
      Q2.hcardT9_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T9_9_2 i) (Q2.hfix9_9_2 i) _)
      colCert_9_9_0.hD ?_).symm
  rw [alnId_9 j hj]


theorem leaf_9_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 9 []).length)
    (hq : (normIsRep.getD 9 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨9, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨9, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨9, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨9, by decide⟩ (listedAt ⟨9, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T9_9
      hfix9_9 hinj9_9 hcardT9_9
      (fun i => conj_mem_of_fixedPoints _ _ (T9_9 i) (hfix9_9 i) _)
      ⟨9, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨9, by decide⟩ (Q2.listedAt ⟨9, by decide⟩
        (alnCheck_rep ⟨9, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T9_9_2 Q2.hfix9_9_2 Q2.hinj9_9_2
      Q2.hcardT9_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T9_9_2 i) (Q2.hfix9_9_2 i) _)
      colCert_9_9_1.hD ?_).symm
  rw [alnId_9 j hj]


theorem leaf_9_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 9 []).length)
    (hq : (normIsRep.getD 9 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨9, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨9, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨9, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨9, by decide⟩ (listedAt ⟨9, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T9_9
      hfix9_9 hinj9_9 hcardT9_9
      (fun i => conj_mem_of_fixedPoints _ _ (T9_9 i) (hfix9_9 i) _)
      ⟨9, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨9, by decide⟩ (Q2.listedAt ⟨9, by decide⟩
        (alnCheck_rep ⟨9, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T9_9_2 Q2.hfix9_9_2 Q2.hinj9_9_2
      Q2.hcardT9_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T9_9_2 i) (Q2.hfix9_9_2 i) _)
      colCert_9_9_2.hD ?_).symm
  rw [alnId_9 j hj]


theorem leaf_9_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 9 []).length)
    (hq : (normIsRep.getD 9 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨9, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨9, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨9, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨9, by decide⟩ (listedAt ⟨9, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T9_9
      hfix9_9 hinj9_9 hcardT9_9
      (fun i => conj_mem_of_fixedPoints _ _ (T9_9 i) (hfix9_9 i) _)
      ⟨9, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨9, by decide⟩ (Q2.listedAt ⟨9, by decide⟩
        (alnCheck_rep ⟨9, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T9_9_2 Q2.hfix9_9_2 Q2.hinj9_9_2
      Q2.hcardT9_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T9_9_2 i) (Q2.hfix9_9_2 i) _)
      colCert_9_9_3.hD ?_).symm
  rw [alnId_9 j hj]


theorem leaf_9_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 9 []).length)
    (hq : (normIsRep.getD 9 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨9, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨9, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨9, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨9, by decide⟩ (listedAt ⟨9, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T9_9
      hfix9_9 hinj9_9 hcardT9_9
      (fun i => conj_mem_of_fixedPoints _ _ (T9_9 i) (hfix9_9 i) _)
      ⟨9, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨9, by decide⟩ (Q2.listedAt ⟨9, by decide⟩
        (alnCheck_rep ⟨9, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T9_9_2 Q2.hfix9_9_2 Q2.hinj9_9_2
      Q2.hcardT9_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T9_9_2 i) (Q2.hfix9_9_2 i) _)
      colCert_9_9_4.hD ?_).symm
  rw [alnId_9 j hj]


theorem leaf_10_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 10 []).length)
    (hq : (normIsRep.getD 10 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨10, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨10, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨10, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨10, by decide⟩ (listedAt ⟨10, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T10_10
      hfix10_10 hinj10_10 hcardT10_10
      (fun i => conj_mem_of_fixedPoints _ _ (T10_10 i) (hfix10_10 i) _)
      ⟨10, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨10, by decide⟩ (Q2.listedAt ⟨10, by decide⟩
        (alnCheck_rep ⟨10, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T10_10_2 Q2.hfix10_10_2 Q2.hinj10_10_2
      Q2.hcardT10_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T10_10_2 i) (Q2.hfix10_10_2 i) _)
      colCert_10_10_0.hD ?_).symm
  rw [alnId_10 j hj]


theorem leaf_10_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 10 []).length)
    (hq : (normIsRep.getD 10 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨10, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨10, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨10, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨10, by decide⟩ (listedAt ⟨10, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T10_10
      hfix10_10 hinj10_10 hcardT10_10
      (fun i => conj_mem_of_fixedPoints _ _ (T10_10 i) (hfix10_10 i) _)
      ⟨10, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨10, by decide⟩ (Q2.listedAt ⟨10, by decide⟩
        (alnCheck_rep ⟨10, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T10_10_2 Q2.hfix10_10_2 Q2.hinj10_10_2
      Q2.hcardT10_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T10_10_2 i) (Q2.hfix10_10_2 i) _)
      colCert_10_10_1.hD ?_).symm
  rw [alnId_10 j hj]


theorem leaf_10_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 10 []).length)
    (hq : (normIsRep.getD 10 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨10, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨10, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨10, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨10, by decide⟩ (listedAt ⟨10, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T10_10
      hfix10_10 hinj10_10 hcardT10_10
      (fun i => conj_mem_of_fixedPoints _ _ (T10_10 i) (hfix10_10 i) _)
      ⟨10, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨10, by decide⟩ (Q2.listedAt ⟨10, by decide⟩
        (alnCheck_rep ⟨10, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T10_10_2 Q2.hfix10_10_2 Q2.hinj10_10_2
      Q2.hcardT10_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T10_10_2 i) (Q2.hfix10_10_2 i) _)
      colCert_10_10_2.hD ?_).symm
  rw [alnId_10 j hj]


theorem leaf_10_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 10 []).length)
    (hq : (normIsRep.getD 10 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨10, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨10, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨10, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨10, by decide⟩ (listedAt ⟨10, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T10_10
      hfix10_10 hinj10_10 hcardT10_10
      (fun i => conj_mem_of_fixedPoints _ _ (T10_10 i) (hfix10_10 i) _)
      ⟨10, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨10, by decide⟩ (Q2.listedAt ⟨10, by decide⟩
        (alnCheck_rep ⟨10, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T10_10_2 Q2.hfix10_10_2 Q2.hinj10_10_2
      Q2.hcardT10_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T10_10_2 i) (Q2.hfix10_10_2 i) _)
      colCert_10_10_3.hD ?_).symm
  rw [alnId_10 j hj]


theorem leaf_10_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 10 []).length)
    (hq : (normIsRep.getD 10 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨10, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨10, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨10, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨10, by decide⟩ (listedAt ⟨10, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T10_10
      hfix10_10 hinj10_10 hcardT10_10
      (fun i => conj_mem_of_fixedPoints _ _ (T10_10 i) (hfix10_10 i) _)
      ⟨10, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨10, by decide⟩ (Q2.listedAt ⟨10, by decide⟩
        (alnCheck_rep ⟨10, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T10_10_2 Q2.hfix10_10_2 Q2.hinj10_10_2
      Q2.hcardT10_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T10_10_2 i) (Q2.hfix10_10_2 i) _)
      colCert_10_10_4.hD ?_).symm
  rw [alnId_10 j hj]


theorem leaf_11_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 11 []).length)
    (hq : (normIsRep.getD 11 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨11, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨11, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨11, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨11, by decide⟩ (listedAt ⟨11, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T11_11
      hfix11_11 hinj11_11 hcardT11_11
      (fun i => conj_mem_of_fixedPoints _ _ (T11_11 i) (hfix11_11 i) _)
      ⟨11, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨11, by decide⟩ (Q2.listedAt ⟨11, by decide⟩
        (alnCheck_rep ⟨11, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T11_11_2 Q2.hfix11_11_2 Q2.hinj11_11_2
      Q2.hcardT11_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T11_11_2 i) (Q2.hfix11_11_2 i) _)
      colCert_11_11_0.hD ?_).symm
  rw [alnId_11 j hj]


theorem leaf_11_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 11 []).length)
    (hq : (normIsRep.getD 11 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨11, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨11, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨11, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨11, by decide⟩ (listedAt ⟨11, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T11_11
      hfix11_11 hinj11_11 hcardT11_11
      (fun i => conj_mem_of_fixedPoints _ _ (T11_11 i) (hfix11_11 i) _)
      ⟨11, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨11, by decide⟩ (Q2.listedAt ⟨11, by decide⟩
        (alnCheck_rep ⟨11, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T11_11_2 Q2.hfix11_11_2 Q2.hinj11_11_2
      Q2.hcardT11_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T11_11_2 i) (Q2.hfix11_11_2 i) _)
      colCert_11_11_1.hD ?_).symm
  rw [alnId_11 j hj]


theorem leaf_11_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 11 []).length)
    (hq : (normIsRep.getD 11 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨11, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨11, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨11, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨11, by decide⟩ (listedAt ⟨11, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T11_11
      hfix11_11 hinj11_11 hcardT11_11
      (fun i => conj_mem_of_fixedPoints _ _ (T11_11 i) (hfix11_11 i) _)
      ⟨11, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨11, by decide⟩ (Q2.listedAt ⟨11, by decide⟩
        (alnCheck_rep ⟨11, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T11_11_2 Q2.hfix11_11_2 Q2.hinj11_11_2
      Q2.hcardT11_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T11_11_2 i) (Q2.hfix11_11_2 i) _)
      colCert_11_11_2.hD ?_).symm
  rw [alnId_11 j hj]


theorem leaf_11_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 11 []).length)
    (hq : (normIsRep.getD 11 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨11, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨11, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨11, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨11, by decide⟩ (listedAt ⟨11, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T11_11
      hfix11_11 hinj11_11 hcardT11_11
      (fun i => conj_mem_of_fixedPoints _ _ (T11_11 i) (hfix11_11 i) _)
      ⟨11, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨11, by decide⟩ (Q2.listedAt ⟨11, by decide⟩
        (alnCheck_rep ⟨11, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T11_11_2 Q2.hfix11_11_2 Q2.hinj11_11_2
      Q2.hcardT11_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T11_11_2 i) (Q2.hfix11_11_2 i) _)
      colCert_11_11_3.hD ?_).symm
  rw [alnId_11 j hj]


theorem leaf_11_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 11 []).length)
    (hq : (normIsRep.getD 11 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨11, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨11, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨11, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨11, by decide⟩ (listedAt ⟨11, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T11_11
      hfix11_11 hinj11_11 hcardT11_11
      (fun i => conj_mem_of_fixedPoints _ _ (T11_11 i) (hfix11_11 i) _)
      ⟨11, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨11, by decide⟩ (Q2.listedAt ⟨11, by decide⟩
        (alnCheck_rep ⟨11, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T11_11_2 Q2.hfix11_11_2 Q2.hinj11_11_2
      Q2.hcardT11_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T11_11_2 i) (Q2.hfix11_11_2 i) _)
      colCert_11_11_4.hD ?_).symm
  rw [alnId_11 j hj]


theorem leaf_12_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 12 []).length)
    (hq : (normIsRep.getD 12 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨12, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨12, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨12, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨12, by decide⟩ (listedAt ⟨12, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T12_12
      hfix12_12 hinj12_12 hcardT12_12
      (fun i => conj_mem_of_fixedPoints _ _ (T12_12 i) (hfix12_12 i) _)
      ⟨12, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨12, by decide⟩ (Q2.listedAt ⟨12, by decide⟩
        (alnCheck_rep ⟨12, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T12_12_2 Q2.hfix12_12_2 Q2.hinj12_12_2
      Q2.hcardT12_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T12_12_2 i) (Q2.hfix12_12_2 i) _)
      colCert_12_12_0.hD ?_).symm
  rw [alnId_12 j hj]


theorem leaf_12_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 12 []).length)
    (hq : (normIsRep.getD 12 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨12, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨12, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨12, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨12, by decide⟩ (listedAt ⟨12, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T12_12
      hfix12_12 hinj12_12 hcardT12_12
      (fun i => conj_mem_of_fixedPoints _ _ (T12_12 i) (hfix12_12 i) _)
      ⟨12, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨12, by decide⟩ (Q2.listedAt ⟨12, by decide⟩
        (alnCheck_rep ⟨12, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T12_12_2 Q2.hfix12_12_2 Q2.hinj12_12_2
      Q2.hcardT12_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T12_12_2 i) (Q2.hfix12_12_2 i) _)
      colCert_12_12_1.hD ?_).symm
  rw [alnId_12 j hj]


theorem leaf_12_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 12 []).length)
    (hq : (normIsRep.getD 12 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨12, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨12, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨12, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨12, by decide⟩ (listedAt ⟨12, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T12_12
      hfix12_12 hinj12_12 hcardT12_12
      (fun i => conj_mem_of_fixedPoints _ _ (T12_12 i) (hfix12_12 i) _)
      ⟨12, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨12, by decide⟩ (Q2.listedAt ⟨12, by decide⟩
        (alnCheck_rep ⟨12, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T12_12_2 Q2.hfix12_12_2 Q2.hinj12_12_2
      Q2.hcardT12_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T12_12_2 i) (Q2.hfix12_12_2 i) _)
      colCert_12_12_2.hD ?_).symm
  rw [alnId_12 j hj]


theorem leaf_12_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 12 []).length)
    (hq : (normIsRep.getD 12 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨12, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨12, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨12, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨12, by decide⟩ (listedAt ⟨12, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T12_12
      hfix12_12 hinj12_12 hcardT12_12
      (fun i => conj_mem_of_fixedPoints _ _ (T12_12 i) (hfix12_12 i) _)
      ⟨12, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨12, by decide⟩ (Q2.listedAt ⟨12, by decide⟩
        (alnCheck_rep ⟨12, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T12_12_2 Q2.hfix12_12_2 Q2.hinj12_12_2
      Q2.hcardT12_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T12_12_2 i) (Q2.hfix12_12_2 i) _)
      colCert_12_12_3.hD ?_).symm
  rw [alnId_12 j hj]


theorem leaf_12_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 12 []).length)
    (hq : (normIsRep.getD 12 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨12, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨12, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨12, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨12, by decide⟩ (listedAt ⟨12, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T12_12
      hfix12_12 hinj12_12 hcardT12_12
      (fun i => conj_mem_of_fixedPoints _ _ (T12_12 i) (hfix12_12 i) _)
      ⟨12, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨12, by decide⟩ (Q2.listedAt ⟨12, by decide⟩
        (alnCheck_rep ⟨12, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T12_12_2 Q2.hfix12_12_2 Q2.hinj12_12_2
      Q2.hcardT12_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T12_12_2 i) (Q2.hfix12_12_2 i) _)
      colCert_12_12_4.hD ?_).symm
  rw [alnId_12 j hj]


theorem leaf_13_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T13_1
      hfix13_1 hinj13_1 hcardT13_1
      (fun i => conj_mem_of_fixedPoints _ _ (T13_1 i) (hfix13_1 i) _)
      ⟨13, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T13_1_2 Q2.hfix13_1_2 Q2.hinj13_1_2
      Q2.hcardT13_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_1_2 i) (Q2.hfix13_1_2 i) _)
      colCert_13_1_0.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T13_1
      hfix13_1 hinj13_1 hcardT13_1
      (fun i => conj_mem_of_fixedPoints _ _ (T13_1 i) (hfix13_1 i) _)
      ⟨13, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T13_1_2 Q2.hfix13_1_2 Q2.hinj13_1_2
      Q2.hcardT13_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_1_2 i) (Q2.hfix13_1_2 i) _)
      colCert_13_1_1.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T13_1
      hfix13_1 hinj13_1 hcardT13_1
      (fun i => conj_mem_of_fixedPoints _ _ (T13_1 i) (hfix13_1 i) _)
      ⟨13, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T13_1_2 Q2.hfix13_1_2 Q2.hinj13_1_2
      Q2.hcardT13_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_1_2 i) (Q2.hfix13_1_2 i) _)
      colCert_13_1_2.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T13_1
      hfix13_1 hinj13_1 hcardT13_1
      (fun i => conj_mem_of_fixedPoints _ _ (T13_1 i) (hfix13_1 i) _)
      ⟨13, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T13_1_2 Q2.hfix13_1_2 Q2.hinj13_1_2
      Q2.hcardT13_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_1_2 i) (Q2.hfix13_1_2 i) _)
      colCert_13_1_3.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T13_1
      hfix13_1 hinj13_1 hcardT13_1
      (fun i => conj_mem_of_fixedPoints _ _ (T13_1 i) (hfix13_1 i) _)
      ⟨13, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T13_1_2 Q2.hfix13_1_2 Q2.hinj13_1_2
      Q2.hcardT13_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_1_2 i) (Q2.hfix13_1_2 i) _)
      colCert_13_1_4.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T13_6
      hfix13_6 hinj13_6 hcardT13_6
      (fun i => conj_mem_of_fixedPoints _ _ (T13_6 i) (hfix13_6 i) _)
      ⟨13, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T13_6_2 Q2.hfix13_6_2 Q2.hinj13_6_2
      Q2.hcardT13_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_6_2 i) (Q2.hfix13_6_2 i) _)
      colCert_13_6_0.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T13_6
      hfix13_6 hinj13_6 hcardT13_6
      (fun i => conj_mem_of_fixedPoints _ _ (T13_6 i) (hfix13_6 i) _)
      ⟨13, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T13_6_2 Q2.hfix13_6_2 Q2.hinj13_6_2
      Q2.hcardT13_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_6_2 i) (Q2.hfix13_6_2 i) _)
      colCert_13_6_1.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T13_6
      hfix13_6 hinj13_6 hcardT13_6
      (fun i => conj_mem_of_fixedPoints _ _ (T13_6 i) (hfix13_6 i) _)
      ⟨13, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T13_6_2 Q2.hfix13_6_2 Q2.hinj13_6_2
      Q2.hcardT13_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_6_2 i) (Q2.hfix13_6_2 i) _)
      colCert_13_6_2.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T13_6
      hfix13_6 hinj13_6 hcardT13_6
      (fun i => conj_mem_of_fixedPoints _ _ (T13_6 i) (hfix13_6 i) _)
      ⟨13, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T13_6_2 Q2.hfix13_6_2 Q2.hinj13_6_2
      Q2.hcardT13_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_6_2 i) (Q2.hfix13_6_2 i) _)
      colCert_13_6_3.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T13_6
      hfix13_6 hinj13_6 hcardT13_6
      (fun i => conj_mem_of_fixedPoints _ _ (T13_6 i) (hfix13_6 i) _)
      ⟨13, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T13_6_2 Q2.hfix13_6_2 Q2.hinj13_6_2
      Q2.hcardT13_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_6_2 i) (Q2.hfix13_6_2 i) _)
      colCert_13_6_4.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T13_7
      hfix13_7 hinj13_7 hcardT13_7
      (fun i => conj_mem_of_fixedPoints _ _ (T13_7 i) (hfix13_7 i) _)
      ⟨13, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T13_7_2 Q2.hfix13_7_2 Q2.hinj13_7_2
      Q2.hcardT13_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_7_2 i) (Q2.hfix13_7_2 i) _)
      colCert_13_7_0.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T13_7
      hfix13_7 hinj13_7 hcardT13_7
      (fun i => conj_mem_of_fixedPoints _ _ (T13_7 i) (hfix13_7 i) _)
      ⟨13, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T13_7_2 Q2.hfix13_7_2 Q2.hinj13_7_2
      Q2.hcardT13_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_7_2 i) (Q2.hfix13_7_2 i) _)
      colCert_13_7_1.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T13_7
      hfix13_7 hinj13_7 hcardT13_7
      (fun i => conj_mem_of_fixedPoints _ _ (T13_7 i) (hfix13_7 i) _)
      ⟨13, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T13_7_2 Q2.hfix13_7_2 Q2.hinj13_7_2
      Q2.hcardT13_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_7_2 i) (Q2.hfix13_7_2 i) _)
      colCert_13_7_2.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T13_7
      hfix13_7 hinj13_7 hcardT13_7
      (fun i => conj_mem_of_fixedPoints _ _ (T13_7 i) (hfix13_7 i) _)
      ⟨13, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T13_7_2 Q2.hfix13_7_2 Q2.hinj13_7_2
      Q2.hcardT13_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_7_2 i) (Q2.hfix13_7_2 i) _)
      colCert_13_7_3.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T13_7
      hfix13_7 hinj13_7 hcardT13_7
      (fun i => conj_mem_of_fixedPoints _ _ (T13_7 i) (hfix13_7 i) _)
      ⟨13, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T13_7_2 Q2.hfix13_7_2 Q2.hinj13_7_2
      Q2.hcardT13_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_7_2 i) (Q2.hfix13_7_2 i) _)
      colCert_13_7_4.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T13_8
      hfix13_8 hinj13_8 hcardT13_8
      (fun i => conj_mem_of_fixedPoints _ _ (T13_8 i) (hfix13_8 i) _)
      ⟨13, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T13_8_2 Q2.hfix13_8_2 Q2.hinj13_8_2
      Q2.hcardT13_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_8_2 i) (Q2.hfix13_8_2 i) _)
      colCert_13_8_0.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T13_8
      hfix13_8 hinj13_8 hcardT13_8
      (fun i => conj_mem_of_fixedPoints _ _ (T13_8 i) (hfix13_8 i) _)
      ⟨13, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T13_8_2 Q2.hfix13_8_2 Q2.hinj13_8_2
      Q2.hcardT13_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_8_2 i) (Q2.hfix13_8_2 i) _)
      colCert_13_8_1.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T13_8
      hfix13_8 hinj13_8 hcardT13_8
      (fun i => conj_mem_of_fixedPoints _ _ (T13_8 i) (hfix13_8 i) _)
      ⟨13, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T13_8_2 Q2.hfix13_8_2 Q2.hinj13_8_2
      Q2.hcardT13_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_8_2 i) (Q2.hfix13_8_2 i) _)
      colCert_13_8_2.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T13_8
      hfix13_8 hinj13_8 hcardT13_8
      (fun i => conj_mem_of_fixedPoints _ _ (T13_8 i) (hfix13_8 i) _)
      ⟨13, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T13_8_2 Q2.hfix13_8_2 Q2.hinj13_8_2
      Q2.hcardT13_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_8_2 i) (Q2.hfix13_8_2 i) _)
      colCert_13_8_3.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T13_8
      hfix13_8 hinj13_8 hcardT13_8
      (fun i => conj_mem_of_fixedPoints _ _ (T13_8 i) (hfix13_8 i) _)
      ⟨13, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T13_8_2 Q2.hfix13_8_2 Q2.hinj13_8_2
      Q2.hcardT13_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_8_2 i) (Q2.hfix13_8_2 i) _)
      colCert_13_8_4.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T13_9
      hfix13_9 hinj13_9 hcardT13_9
      (fun i => conj_mem_of_fixedPoints _ _ (T13_9 i) (hfix13_9 i) _)
      ⟨13, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T13_9_2 Q2.hfix13_9_2 Q2.hinj13_9_2
      Q2.hcardT13_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_9_2 i) (Q2.hfix13_9_2 i) _)
      colCert_13_9_0.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T13_9
      hfix13_9 hinj13_9 hcardT13_9
      (fun i => conj_mem_of_fixedPoints _ _ (T13_9 i) (hfix13_9 i) _)
      ⟨13, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T13_9_2 Q2.hfix13_9_2 Q2.hinj13_9_2
      Q2.hcardT13_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_9_2 i) (Q2.hfix13_9_2 i) _)
      colCert_13_9_1.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T13_9
      hfix13_9 hinj13_9 hcardT13_9
      (fun i => conj_mem_of_fixedPoints _ _ (T13_9 i) (hfix13_9 i) _)
      ⟨13, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T13_9_2 Q2.hfix13_9_2 Q2.hinj13_9_2
      Q2.hcardT13_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_9_2 i) (Q2.hfix13_9_2 i) _)
      colCert_13_9_2.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T13_9
      hfix13_9 hinj13_9 hcardT13_9
      (fun i => conj_mem_of_fixedPoints _ _ (T13_9 i) (hfix13_9 i) _)
      ⟨13, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T13_9_2 Q2.hfix13_9_2 Q2.hinj13_9_2
      Q2.hcardT13_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_9_2 i) (Q2.hfix13_9_2 i) _)
      colCert_13_9_3.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T13_9
      hfix13_9 hinj13_9 hcardT13_9
      (fun i => conj_mem_of_fixedPoints _ _ (T13_9 i) (hfix13_9 i) _)
      ⟨13, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T13_9_2 Q2.hfix13_9_2 Q2.hinj13_9_2
      Q2.hcardT13_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_9_2 i) (Q2.hfix13_9_2 i) _)
      colCert_13_9_4.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T13_10
      hfix13_10 hinj13_10 hcardT13_10
      (fun i => conj_mem_of_fixedPoints _ _ (T13_10 i) (hfix13_10 i) _)
      ⟨13, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T13_10_2 Q2.hfix13_10_2 Q2.hinj13_10_2
      Q2.hcardT13_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_10_2 i) (Q2.hfix13_10_2 i) _)
      colCert_13_10_0.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T13_10
      hfix13_10 hinj13_10 hcardT13_10
      (fun i => conj_mem_of_fixedPoints _ _ (T13_10 i) (hfix13_10 i) _)
      ⟨13, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T13_10_2 Q2.hfix13_10_2 Q2.hinj13_10_2
      Q2.hcardT13_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_10_2 i) (Q2.hfix13_10_2 i) _)
      colCert_13_10_1.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T13_10
      hfix13_10 hinj13_10 hcardT13_10
      (fun i => conj_mem_of_fixedPoints _ _ (T13_10 i) (hfix13_10 i) _)
      ⟨13, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T13_10_2 Q2.hfix13_10_2 Q2.hinj13_10_2
      Q2.hcardT13_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_10_2 i) (Q2.hfix13_10_2 i) _)
      colCert_13_10_2.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T13_10
      hfix13_10 hinj13_10 hcardT13_10
      (fun i => conj_mem_of_fixedPoints _ _ (T13_10 i) (hfix13_10 i) _)
      ⟨13, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T13_10_2 Q2.hfix13_10_2 Q2.hinj13_10_2
      Q2.hcardT13_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_10_2 i) (Q2.hfix13_10_2 i) _)
      colCert_13_10_3.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T13_10
      hfix13_10 hinj13_10 hcardT13_10
      (fun i => conj_mem_of_fixedPoints _ _ (T13_10 i) (hfix13_10 i) _)
      ⟨13, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T13_10_2 Q2.hfix13_10_2 Q2.hinj13_10_2
      Q2.hcardT13_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_10_2 i) (Q2.hfix13_10_2 i) _)
      colCert_13_10_4.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_0 (hp : 0 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 0 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 0 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_0.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_1 (hp : 1 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 1 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 1 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_1.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_2 (hp : 2 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 2 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 2 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_2.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_3 (hp : 3 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 3 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 3 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_3.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_4 (hp : 4 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 4 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 4 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_4.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_5 (hp : 5 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 5 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 5 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨13, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T13_13 = colFn colCertDiv_13_13_5.D1 (m := 5) from colCertDiv_13_13_5.bind1,
    show colData2 (⟨13, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 5 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T13_13_2 = colFn colCertDiv_13_13_5.D2 (m := 5) from colCertDiv_13_13_5.bind2]
  rw [alnId_13 j hj]
  exact fastcode_of_tau ⟨13, by decide⟩ _ _ _
    ((alnId_13 j hj) ▸ Q2.listedAt (⟨13, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨13, by decide⟩ : Fin 148) hj hq).1) colCertDiv_13_13_5_tau_match


theorem leaf_13_13_6 (hp : 6 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 6 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 6 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨13, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T13_13 = colFn colCertDiv_13_13_6.D1 (m := 5) from colCertDiv_13_13_6.bind1,
    show colData2 (⟨13, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 6 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T13_13_2 = colFn colCertDiv_13_13_6.D2 (m := 5) from colCertDiv_13_13_6.bind2]
  rw [alnId_13 j hj]
  exact fastcode_of_tau ⟨13, by decide⟩ _ _ _
    ((alnId_13 j hj) ▸ Q2.listedAt (⟨13, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨13, by decide⟩ : Fin 148) hj hq).1) colCertDiv_13_13_6_tau_match


theorem leaf_13_13_7 (hp : 7 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 7 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 7 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨13, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T13_13 = colFn colCertDiv_13_13_7.D1 (m := 5) from colCertDiv_13_13_7.bind1,
    show colData2 (⟨13, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 7 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T13_13_2 = colFn colCertDiv_13_13_7.D2 (m := 5) from colCertDiv_13_13_7.bind2]
  rw [alnId_13 j hj]
  exact fastcode_of_tau ⟨13, by decide⟩ _ _ _
    ((alnId_13 j hj) ▸ Q2.listedAt (⟨13, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨13, by decide⟩ : Fin 148) hj hq).1) colCertDiv_13_13_7_tau_match


theorem leaf_13_13_8 (hp : 8 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 8 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 8 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨13, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T13_13 = colFn colCertDiv_13_13_8.D1 (m := 5) from colCertDiv_13_13_8.bind1,
    show colData2 (⟨13, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 8 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T13_13_2 = colFn colCertDiv_13_13_8.D2 (m := 5) from colCertDiv_13_13_8.bind2]
  rw [alnId_13 j hj]
  exact fastcode_of_tau ⟨13, by decide⟩ _ _ _
    ((alnId_13 j hj) ▸ Q2.listedAt (⟨13, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨13, by decide⟩ : Fin 148) hj hq).1) colCertDiv_13_13_8_tau_match


theorem leaf_13_13_9 (hp : 9 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 9 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 9 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_9.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_10 (hp : 10 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 10 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 10 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_10.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_11 (hp : 11 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 11 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 11 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_11.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_12 (hp : 12 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 12 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 12 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_12.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_13 (hp : 13 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 13 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 13 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_13.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_14 (hp : 14 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 14 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 14 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_14.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_15 (hp : 15 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 15 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 15 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_15.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_16 (hp : 16 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 16 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 16 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_16.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_17 (hp : 17 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 17 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 17 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_17.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_18 (hp : 18 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 18 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 18 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_18.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_19 (hp : 19 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 19 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 19 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_19.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_20 (hp : 20 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 20 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 20 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_20.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_21 (hp : 21 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 21 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 21 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_21.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_22 (hp : 22 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 22 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 22 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_22.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_23 (hp : 23 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 23 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 23 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_23.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_13_13_24 (hp : 24 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 13 []).length)
    (hq : (normIsRep.getD 13 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 24 hp)
        (rowE2 (⟨13, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp))
        (rowE1 (⟨13, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨13, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨13, by decide⟩ (listedAt ⟨13, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp)) T13_13
      hfix13_13 hinj13_13 hcardT13_13
      (fun i => conj_mem_of_fixedPoints _ _ (T13_13 i) (hfix13_13 i) _)
      ⟨13, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨13, by decide⟩ (Q2.listedAt ⟨13, by decide⟩
        (alnCheck_rep ⟨13, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 24 hp) Q2.T13_13_2 Q2.hfix13_13_2 Q2.hinj13_13_2
      Q2.hcardT13_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T13_13_2 i) (Q2.hfix13_13_2 i) _)
      colCert_13_13_24.hD ?_).symm
  rw [alnId_13 j hj]


theorem leaf_14_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T14_2
      hfix14_2 hinj14_2 hcardT14_2
      (fun i => conj_mem_of_fixedPoints _ _ (T14_2 i) (hfix14_2 i) _)
      ⟨14, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T14_2_2 Q2.hfix14_2_2 Q2.hinj14_2_2
      Q2.hcardT14_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_2_2 i) (Q2.hfix14_2_2 i) _)
      colCert_14_2_0.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T14_2
      hfix14_2 hinj14_2 hcardT14_2
      (fun i => conj_mem_of_fixedPoints _ _ (T14_2 i) (hfix14_2 i) _)
      ⟨14, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T14_2_2 Q2.hfix14_2_2 Q2.hinj14_2_2
      Q2.hcardT14_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_2_2 i) (Q2.hfix14_2_2 i) _)
      colCert_14_2_1.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T14_2
      hfix14_2 hinj14_2 hcardT14_2
      (fun i => conj_mem_of_fixedPoints _ _ (T14_2 i) (hfix14_2 i) _)
      ⟨14, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T14_2_2 Q2.hfix14_2_2 Q2.hinj14_2_2
      Q2.hcardT14_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_2_2 i) (Q2.hfix14_2_2 i) _)
      colCert_14_2_2.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T14_2
      hfix14_2 hinj14_2 hcardT14_2
      (fun i => conj_mem_of_fixedPoints _ _ (T14_2 i) (hfix14_2 i) _)
      ⟨14, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T14_2_2 Q2.hfix14_2_2 Q2.hinj14_2_2
      Q2.hcardT14_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_2_2 i) (Q2.hfix14_2_2 i) _)
      colCert_14_2_3.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T14_2
      hfix14_2 hinj14_2 hcardT14_2
      (fun i => conj_mem_of_fixedPoints _ _ (T14_2 i) (hfix14_2 i) _)
      ⟨14, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T14_2_2 Q2.hfix14_2_2 Q2.hinj14_2_2
      Q2.hcardT14_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_2_2 i) (Q2.hfix14_2_2 i) _)
      colCert_14_2_4.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T14_3
      hfix14_3 hinj14_3 hcardT14_3
      (fun i => conj_mem_of_fixedPoints _ _ (T14_3 i) (hfix14_3 i) _)
      ⟨14, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T14_3_2 Q2.hfix14_3_2 Q2.hinj14_3_2
      Q2.hcardT14_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_3_2 i) (Q2.hfix14_3_2 i) _)
      colCert_14_3_0.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T14_3
      hfix14_3 hinj14_3 hcardT14_3
      (fun i => conj_mem_of_fixedPoints _ _ (T14_3 i) (hfix14_3 i) _)
      ⟨14, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T14_3_2 Q2.hfix14_3_2 Q2.hinj14_3_2
      Q2.hcardT14_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_3_2 i) (Q2.hfix14_3_2 i) _)
      colCert_14_3_1.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T14_3
      hfix14_3 hinj14_3 hcardT14_3
      (fun i => conj_mem_of_fixedPoints _ _ (T14_3 i) (hfix14_3 i) _)
      ⟨14, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T14_3_2 Q2.hfix14_3_2 Q2.hinj14_3_2
      Q2.hcardT14_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_3_2 i) (Q2.hfix14_3_2 i) _)
      colCert_14_3_2.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T14_3
      hfix14_3 hinj14_3 hcardT14_3
      (fun i => conj_mem_of_fixedPoints _ _ (T14_3 i) (hfix14_3 i) _)
      ⟨14, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T14_3_2 Q2.hfix14_3_2 Q2.hinj14_3_2
      Q2.hcardT14_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_3_2 i) (Q2.hfix14_3_2 i) _)
      colCert_14_3_3.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T14_3
      hfix14_3 hinj14_3 hcardT14_3
      (fun i => conj_mem_of_fixedPoints _ _ (T14_3 i) (hfix14_3 i) _)
      ⟨14, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T14_3_2 Q2.hfix14_3_2 Q2.hinj14_3_2
      Q2.hcardT14_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_3_2 i) (Q2.hfix14_3_2 i) _)
      colCert_14_3_4.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T14_4
      hfix14_4 hinj14_4 hcardT14_4
      (fun i => conj_mem_of_fixedPoints _ _ (T14_4 i) (hfix14_4 i) _)
      ⟨14, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T14_4_2 Q2.hfix14_4_2 Q2.hinj14_4_2
      Q2.hcardT14_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_4_2 i) (Q2.hfix14_4_2 i) _)
      colCert_14_4_0.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T14_4
      hfix14_4 hinj14_4 hcardT14_4
      (fun i => conj_mem_of_fixedPoints _ _ (T14_4 i) (hfix14_4 i) _)
      ⟨14, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T14_4_2 Q2.hfix14_4_2 Q2.hinj14_4_2
      Q2.hcardT14_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_4_2 i) (Q2.hfix14_4_2 i) _)
      colCert_14_4_1.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T14_4
      hfix14_4 hinj14_4 hcardT14_4
      (fun i => conj_mem_of_fixedPoints _ _ (T14_4 i) (hfix14_4 i) _)
      ⟨14, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T14_4_2 Q2.hfix14_4_2 Q2.hinj14_4_2
      Q2.hcardT14_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_4_2 i) (Q2.hfix14_4_2 i) _)
      colCert_14_4_2.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T14_4
      hfix14_4 hinj14_4 hcardT14_4
      (fun i => conj_mem_of_fixedPoints _ _ (T14_4 i) (hfix14_4 i) _)
      ⟨14, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T14_4_2 Q2.hfix14_4_2 Q2.hinj14_4_2
      Q2.hcardT14_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_4_2 i) (Q2.hfix14_4_2 i) _)
      colCert_14_4_3.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T14_4
      hfix14_4 hinj14_4 hcardT14_4
      (fun i => conj_mem_of_fixedPoints _ _ (T14_4 i) (hfix14_4 i) _)
      ⟨14, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T14_4_2 Q2.hfix14_4_2 Q2.hinj14_4_2
      Q2.hcardT14_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_4_2 i) (Q2.hfix14_4_2 i) _)
      colCert_14_4_4.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T14_5
      hfix14_5 hinj14_5 hcardT14_5
      (fun i => conj_mem_of_fixedPoints _ _ (T14_5 i) (hfix14_5 i) _)
      ⟨14, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T14_5_2 Q2.hfix14_5_2 Q2.hinj14_5_2
      Q2.hcardT14_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_5_2 i) (Q2.hfix14_5_2 i) _)
      colCert_14_5_0.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T14_5
      hfix14_5 hinj14_5 hcardT14_5
      (fun i => conj_mem_of_fixedPoints _ _ (T14_5 i) (hfix14_5 i) _)
      ⟨14, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T14_5_2 Q2.hfix14_5_2 Q2.hinj14_5_2
      Q2.hcardT14_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_5_2 i) (Q2.hfix14_5_2 i) _)
      colCert_14_5_1.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T14_5
      hfix14_5 hinj14_5 hcardT14_5
      (fun i => conj_mem_of_fixedPoints _ _ (T14_5 i) (hfix14_5 i) _)
      ⟨14, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T14_5_2 Q2.hfix14_5_2 Q2.hinj14_5_2
      Q2.hcardT14_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_5_2 i) (Q2.hfix14_5_2 i) _)
      colCert_14_5_2.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T14_5
      hfix14_5 hinj14_5 hcardT14_5
      (fun i => conj_mem_of_fixedPoints _ _ (T14_5 i) (hfix14_5 i) _)
      ⟨14, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T14_5_2 Q2.hfix14_5_2 Q2.hinj14_5_2
      Q2.hcardT14_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_5_2 i) (Q2.hfix14_5_2 i) _)
      colCert_14_5_3.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T14_5
      hfix14_5 hinj14_5 hcardT14_5
      (fun i => conj_mem_of_fixedPoints _ _ (T14_5 i) (hfix14_5 i) _)
      ⟨14, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T14_5_2 Q2.hfix14_5_2 Q2.hinj14_5_2
      Q2.hcardT14_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_5_2 i) (Q2.hfix14_5_2 i) _)
      colCert_14_5_4.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T14_9
      hfix14_9 hinj14_9 hcardT14_9
      (fun i => conj_mem_of_fixedPoints _ _ (T14_9 i) (hfix14_9 i) _)
      ⟨14, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T14_9_2 Q2.hfix14_9_2 Q2.hinj14_9_2
      Q2.hcardT14_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_9_2 i) (Q2.hfix14_9_2 i) _)
      colCert_14_9_0.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T14_9
      hfix14_9 hinj14_9 hcardT14_9
      (fun i => conj_mem_of_fixedPoints _ _ (T14_9 i) (hfix14_9 i) _)
      ⟨14, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T14_9_2 Q2.hfix14_9_2 Q2.hinj14_9_2
      Q2.hcardT14_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_9_2 i) (Q2.hfix14_9_2 i) _)
      colCert_14_9_1.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T14_9
      hfix14_9 hinj14_9 hcardT14_9
      (fun i => conj_mem_of_fixedPoints _ _ (T14_9 i) (hfix14_9 i) _)
      ⟨14, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T14_9_2 Q2.hfix14_9_2 Q2.hinj14_9_2
      Q2.hcardT14_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_9_2 i) (Q2.hfix14_9_2 i) _)
      colCert_14_9_2.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T14_9
      hfix14_9 hinj14_9 hcardT14_9
      (fun i => conj_mem_of_fixedPoints _ _ (T14_9 i) (hfix14_9 i) _)
      ⟨14, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T14_9_2 Q2.hfix14_9_2 Q2.hinj14_9_2
      Q2.hcardT14_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_9_2 i) (Q2.hfix14_9_2 i) _)
      colCert_14_9_3.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T14_9
      hfix14_9 hinj14_9 hcardT14_9
      (fun i => conj_mem_of_fixedPoints _ _ (T14_9 i) (hfix14_9 i) _)
      ⟨14, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T14_9_2 Q2.hfix14_9_2 Q2.hinj14_9_2
      Q2.hcardT14_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_9_2 i) (Q2.hfix14_9_2 i) _)
      colCert_14_9_4.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T14_11
      hfix14_11 hinj14_11 hcardT14_11
      (fun i => conj_mem_of_fixedPoints _ _ (T14_11 i) (hfix14_11 i) _)
      ⟨14, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T14_11_2 Q2.hfix14_11_2 Q2.hinj14_11_2
      Q2.hcardT14_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_11_2 i) (Q2.hfix14_11_2 i) _)
      colCert_14_11_0.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T14_11
      hfix14_11 hinj14_11 hcardT14_11
      (fun i => conj_mem_of_fixedPoints _ _ (T14_11 i) (hfix14_11 i) _)
      ⟨14, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T14_11_2 Q2.hfix14_11_2 Q2.hinj14_11_2
      Q2.hcardT14_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_11_2 i) (Q2.hfix14_11_2 i) _)
      colCert_14_11_1.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T14_11
      hfix14_11 hinj14_11 hcardT14_11
      (fun i => conj_mem_of_fixedPoints _ _ (T14_11 i) (hfix14_11 i) _)
      ⟨14, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T14_11_2 Q2.hfix14_11_2 Q2.hinj14_11_2
      Q2.hcardT14_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_11_2 i) (Q2.hfix14_11_2 i) _)
      colCert_14_11_2.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T14_11
      hfix14_11 hinj14_11 hcardT14_11
      (fun i => conj_mem_of_fixedPoints _ _ (T14_11 i) (hfix14_11 i) _)
      ⟨14, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T14_11_2 Q2.hfix14_11_2 Q2.hinj14_11_2
      Q2.hcardT14_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_11_2 i) (Q2.hfix14_11_2 i) _)
      colCert_14_11_3.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T14_11
      hfix14_11 hinj14_11 hcardT14_11
      (fun i => conj_mem_of_fixedPoints _ _ (T14_11 i) (hfix14_11 i) _)
      ⟨14, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T14_11_2 Q2.hfix14_11_2 Q2.hinj14_11_2
      Q2.hcardT14_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_11_2 i) (Q2.hfix14_11_2 i) _)
      colCert_14_11_4.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_0 (hp : 0 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 0 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 0 (transLenTr ⟨14, by decide⟩ 0 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 0 (transLenTr ⟨14, by decide⟩ 0 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 0 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_0.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_1 (hp : 1 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 1 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 1 (transLenTr ⟨14, by decide⟩ 1 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 1 (transLenTr ⟨14, by decide⟩ 1 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 1 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_1.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_2 (hp : 2 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 2 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 2 (transLenTr ⟨14, by decide⟩ 2 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 2 (transLenTr ⟨14, by decide⟩ 2 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 2 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_2.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_3 (hp : 3 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 3 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 3 (transLenTr ⟨14, by decide⟩ 3 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 3 (transLenTr ⟨14, by decide⟩ 3 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 3 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_3.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_4 (hp : 4 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 4 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 4 (transLenTr ⟨14, by decide⟩ 4 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 4 (transLenTr ⟨14, by decide⟩ 4 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 4 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_4.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_5 (hp : 5 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 5 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 5 (transLenTr ⟨14, by decide⟩ 5 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 5 (transLenTr ⟨14, by decide⟩ 5 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 5 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_5.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_6 (hp : 6 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 6 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 6 (transLenTr ⟨14, by decide⟩ 6 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 6 (transLenTr ⟨14, by decide⟩ 6 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 6 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_6.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_7 (hp : 7 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 7 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 7 (transLenTr ⟨14, by decide⟩ 7 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 7 (transLenTr ⟨14, by decide⟩ 7 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 7 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_7.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_8 (hp : 8 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 8 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 8 (transLenTr ⟨14, by decide⟩ 8 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 8 (transLenTr ⟨14, by decide⟩ 8 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 8 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_8.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_9 (hp : 9 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 9 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 9 (transLenTr ⟨14, by decide⟩ 9 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 9 (transLenTr ⟨14, by decide⟩ 9 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 9 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_9.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_10 (hp : 10 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 10 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 10 (transLenTr ⟨14, by decide⟩ 10 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 10 (transLenTr ⟨14, by decide⟩ 10 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 10 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_10.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_11 (hp : 11 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 11 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 11 (transLenTr ⟨14, by decide⟩ 11 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 11 (transLenTr ⟨14, by decide⟩ 11 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 11 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_11.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_12 (hp : 12 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 12 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 12 (transLenTr ⟨14, by decide⟩ 12 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 12 (transLenTr ⟨14, by decide⟩ 12 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 12 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_12.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_13 (hp : 13 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 13 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 13 (transLenTr ⟨14, by decide⟩ 13 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 13 (transLenTr ⟨14, by decide⟩ 13 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 13 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_13.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_14 (hp : 14 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 14 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 14 (transLenTr ⟨14, by decide⟩ 14 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 14 (transLenTr ⟨14, by decide⟩ 14 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 14 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_14.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_15 (hp : 15 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 15 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 15 (transLenTr ⟨14, by decide⟩ 15 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 15 (transLenTr ⟨14, by decide⟩ 15 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 15 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_15.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_16 (hp : 16 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 16 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 16 (transLenTr ⟨14, by decide⟩ 16 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 16 (transLenTr ⟨14, by decide⟩ 16 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 16 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_16.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_17 (hp : 17 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 17 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 17 (transLenTr ⟨14, by decide⟩ 17 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 17 (transLenTr ⟨14, by decide⟩ 17 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 17 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_17.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_18 (hp : 18 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 18 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 18 (transLenTr ⟨14, by decide⟩ 18 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 18 (transLenTr ⟨14, by decide⟩ 18 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 18 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_18.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_19 (hp : 19 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 19 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 19 (transLenTr ⟨14, by decide⟩ 19 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 19 (transLenTr ⟨14, by decide⟩ 19 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 19 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_19.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_20 (hp : 20 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 20 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 20 (transLenTr ⟨14, by decide⟩ 20 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 20 (transLenTr ⟨14, by decide⟩ 20 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 20 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_20.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_21 (hp : 21 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 21 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 21 (transLenTr ⟨14, by decide⟩ 21 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 21 (transLenTr ⟨14, by decide⟩ 21 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 21 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_21.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_22 (hp : 22 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 22 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 22 (transLenTr ⟨14, by decide⟩ 22 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 22 (transLenTr ⟨14, by decide⟩ 22 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 22 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_22.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_23 (hp : 23 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 23 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 23 (transLenTr ⟨14, by decide⟩ 23 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 23 (transLenTr ⟨14, by decide⟩ 23 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 23 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_23.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_14_14_24 (hp : 24 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 14 []).length)
    (hq : (normIsRep.getD 14 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 24 hp)
        (rowE2 (⟨14, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 24 (transLenTr ⟨14, by decide⟩ 24 hp))
        (rowE1 (⟨14, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨14, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨14, by decide⟩ (listedAt ⟨14, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 24 (transLenTr ⟨14, by decide⟩ 24 hp)) T14_14
      hfix14_14 hinj14_14 hcardT14_14
      (fun i => conj_mem_of_fixedPoints _ _ (T14_14 i) (hfix14_14 i) _)
      ⟨14, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨14, by decide⟩ (Q2.listedAt ⟨14, by decide⟩
        (alnCheck_rep ⟨14, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 24 hp) Q2.T14_14_2 Q2.hfix14_14_2 Q2.hinj14_14_2
      Q2.hcardT14_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T14_14_2 i) (Q2.hfix14_14_2 i) _)
      colCert_14_14_24.hD ?_).symm
  rw [alnId_14 j hj]


theorem leaf_15_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T15_2
      hfix15_2 hinj15_2 hcardT15_2
      (fun i => conj_mem_of_fixedPoints _ _ (T15_2 i) (hfix15_2 i) _)
      ⟨15, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T15_2_2 Q2.hfix15_2_2 Q2.hinj15_2_2
      Q2.hcardT15_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_2_2 i) (Q2.hfix15_2_2 i) _)
      colCert_15_2_0.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T15_2
      hfix15_2 hinj15_2 hcardT15_2
      (fun i => conj_mem_of_fixedPoints _ _ (T15_2 i) (hfix15_2 i) _)
      ⟨15, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T15_2_2 Q2.hfix15_2_2 Q2.hinj15_2_2
      Q2.hcardT15_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_2_2 i) (Q2.hfix15_2_2 i) _)
      colCert_15_2_1.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T15_2
      hfix15_2 hinj15_2 hcardT15_2
      (fun i => conj_mem_of_fixedPoints _ _ (T15_2 i) (hfix15_2 i) _)
      ⟨15, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T15_2_2 Q2.hfix15_2_2 Q2.hinj15_2_2
      Q2.hcardT15_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_2_2 i) (Q2.hfix15_2_2 i) _)
      colCert_15_2_2.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T15_2
      hfix15_2 hinj15_2 hcardT15_2
      (fun i => conj_mem_of_fixedPoints _ _ (T15_2 i) (hfix15_2 i) _)
      ⟨15, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T15_2_2 Q2.hfix15_2_2 Q2.hinj15_2_2
      Q2.hcardT15_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_2_2 i) (Q2.hfix15_2_2 i) _)
      colCert_15_2_3.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T15_2
      hfix15_2 hinj15_2 hcardT15_2
      (fun i => conj_mem_of_fixedPoints _ _ (T15_2 i) (hfix15_2 i) _)
      ⟨15, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T15_2_2 Q2.hfix15_2_2 Q2.hinj15_2_2
      Q2.hcardT15_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_2_2 i) (Q2.hfix15_2_2 i) _)
      colCert_15_2_4.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T15_3
      hfix15_3 hinj15_3 hcardT15_3
      (fun i => conj_mem_of_fixedPoints _ _ (T15_3 i) (hfix15_3 i) _)
      ⟨15, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T15_3_2 Q2.hfix15_3_2 Q2.hinj15_3_2
      Q2.hcardT15_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_3_2 i) (Q2.hfix15_3_2 i) _)
      colCert_15_3_0.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T15_3
      hfix15_3 hinj15_3 hcardT15_3
      (fun i => conj_mem_of_fixedPoints _ _ (T15_3 i) (hfix15_3 i) _)
      ⟨15, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T15_3_2 Q2.hfix15_3_2 Q2.hinj15_3_2
      Q2.hcardT15_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_3_2 i) (Q2.hfix15_3_2 i) _)
      colCert_15_3_1.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T15_3
      hfix15_3 hinj15_3 hcardT15_3
      (fun i => conj_mem_of_fixedPoints _ _ (T15_3 i) (hfix15_3 i) _)
      ⟨15, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T15_3_2 Q2.hfix15_3_2 Q2.hinj15_3_2
      Q2.hcardT15_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_3_2 i) (Q2.hfix15_3_2 i) _)
      colCert_15_3_2.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T15_3
      hfix15_3 hinj15_3 hcardT15_3
      (fun i => conj_mem_of_fixedPoints _ _ (T15_3 i) (hfix15_3 i) _)
      ⟨15, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T15_3_2 Q2.hfix15_3_2 Q2.hinj15_3_2
      Q2.hcardT15_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_3_2 i) (Q2.hfix15_3_2 i) _)
      colCert_15_3_3.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T15_3
      hfix15_3 hinj15_3 hcardT15_3
      (fun i => conj_mem_of_fixedPoints _ _ (T15_3 i) (hfix15_3 i) _)
      ⟨15, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T15_3_2 Q2.hfix15_3_2 Q2.hinj15_3_2
      Q2.hcardT15_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_3_2 i) (Q2.hfix15_3_2 i) _)
      colCert_15_3_4.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T15_4
      hfix15_4 hinj15_4 hcardT15_4
      (fun i => conj_mem_of_fixedPoints _ _ (T15_4 i) (hfix15_4 i) _)
      ⟨15, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T15_4_2 Q2.hfix15_4_2 Q2.hinj15_4_2
      Q2.hcardT15_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_4_2 i) (Q2.hfix15_4_2 i) _)
      colCert_15_4_0.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T15_4
      hfix15_4 hinj15_4 hcardT15_4
      (fun i => conj_mem_of_fixedPoints _ _ (T15_4 i) (hfix15_4 i) _)
      ⟨15, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T15_4_2 Q2.hfix15_4_2 Q2.hinj15_4_2
      Q2.hcardT15_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_4_2 i) (Q2.hfix15_4_2 i) _)
      colCert_15_4_1.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T15_4
      hfix15_4 hinj15_4 hcardT15_4
      (fun i => conj_mem_of_fixedPoints _ _ (T15_4 i) (hfix15_4 i) _)
      ⟨15, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T15_4_2 Q2.hfix15_4_2 Q2.hinj15_4_2
      Q2.hcardT15_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_4_2 i) (Q2.hfix15_4_2 i) _)
      colCert_15_4_2.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T15_4
      hfix15_4 hinj15_4 hcardT15_4
      (fun i => conj_mem_of_fixedPoints _ _ (T15_4 i) (hfix15_4 i) _)
      ⟨15, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T15_4_2 Q2.hfix15_4_2 Q2.hinj15_4_2
      Q2.hcardT15_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_4_2 i) (Q2.hfix15_4_2 i) _)
      colCert_15_4_3.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T15_4
      hfix15_4 hinj15_4 hcardT15_4
      (fun i => conj_mem_of_fixedPoints _ _ (T15_4 i) (hfix15_4 i) _)
      ⟨15, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T15_4_2 Q2.hfix15_4_2 Q2.hinj15_4_2
      Q2.hcardT15_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_4_2 i) (Q2.hfix15_4_2 i) _)
      colCert_15_4_4.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T15_5
      hfix15_5 hinj15_5 hcardT15_5
      (fun i => conj_mem_of_fixedPoints _ _ (T15_5 i) (hfix15_5 i) _)
      ⟨15, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T15_5_2 Q2.hfix15_5_2 Q2.hinj15_5_2
      Q2.hcardT15_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_5_2 i) (Q2.hfix15_5_2 i) _)
      colCert_15_5_0.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T15_5
      hfix15_5 hinj15_5 hcardT15_5
      (fun i => conj_mem_of_fixedPoints _ _ (T15_5 i) (hfix15_5 i) _)
      ⟨15, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T15_5_2 Q2.hfix15_5_2 Q2.hinj15_5_2
      Q2.hcardT15_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_5_2 i) (Q2.hfix15_5_2 i) _)
      colCert_15_5_1.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T15_5
      hfix15_5 hinj15_5 hcardT15_5
      (fun i => conj_mem_of_fixedPoints _ _ (T15_5 i) (hfix15_5 i) _)
      ⟨15, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T15_5_2 Q2.hfix15_5_2 Q2.hinj15_5_2
      Q2.hcardT15_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_5_2 i) (Q2.hfix15_5_2 i) _)
      colCert_15_5_2.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T15_5
      hfix15_5 hinj15_5 hcardT15_5
      (fun i => conj_mem_of_fixedPoints _ _ (T15_5 i) (hfix15_5 i) _)
      ⟨15, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T15_5_2 Q2.hfix15_5_2 Q2.hinj15_5_2
      Q2.hcardT15_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_5_2 i) (Q2.hfix15_5_2 i) _)
      colCert_15_5_3.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T15_5
      hfix15_5 hinj15_5 hcardT15_5
      (fun i => conj_mem_of_fixedPoints _ _ (T15_5 i) (hfix15_5 i) _)
      ⟨15, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T15_5_2 Q2.hfix15_5_2 Q2.hinj15_5_2
      Q2.hcardT15_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_5_2 i) (Q2.hfix15_5_2 i) _)
      colCert_15_5_4.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T15_9
      hfix15_9 hinj15_9 hcardT15_9
      (fun i => conj_mem_of_fixedPoints _ _ (T15_9 i) (hfix15_9 i) _)
      ⟨15, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T15_9_2 Q2.hfix15_9_2 Q2.hinj15_9_2
      Q2.hcardT15_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_9_2 i) (Q2.hfix15_9_2 i) _)
      colCert_15_9_0.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T15_9
      hfix15_9 hinj15_9 hcardT15_9
      (fun i => conj_mem_of_fixedPoints _ _ (T15_9 i) (hfix15_9 i) _)
      ⟨15, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T15_9_2 Q2.hfix15_9_2 Q2.hinj15_9_2
      Q2.hcardT15_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_9_2 i) (Q2.hfix15_9_2 i) _)
      colCert_15_9_1.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T15_9
      hfix15_9 hinj15_9 hcardT15_9
      (fun i => conj_mem_of_fixedPoints _ _ (T15_9 i) (hfix15_9 i) _)
      ⟨15, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T15_9_2 Q2.hfix15_9_2 Q2.hinj15_9_2
      Q2.hcardT15_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_9_2 i) (Q2.hfix15_9_2 i) _)
      colCert_15_9_2.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T15_9
      hfix15_9 hinj15_9 hcardT15_9
      (fun i => conj_mem_of_fixedPoints _ _ (T15_9 i) (hfix15_9 i) _)
      ⟨15, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T15_9_2 Q2.hfix15_9_2 Q2.hinj15_9_2
      Q2.hcardT15_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_9_2 i) (Q2.hfix15_9_2 i) _)
      colCert_15_9_3.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T15_9
      hfix15_9 hinj15_9 hcardT15_9
      (fun i => conj_mem_of_fixedPoints _ _ (T15_9 i) (hfix15_9 i) _)
      ⟨15, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T15_9_2 Q2.hfix15_9_2 Q2.hinj15_9_2
      Q2.hcardT15_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_9_2 i) (Q2.hfix15_9_2 i) _)
      colCert_15_9_4.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T15_11
      hfix15_11 hinj15_11 hcardT15_11
      (fun i => conj_mem_of_fixedPoints _ _ (T15_11 i) (hfix15_11 i) _)
      ⟨15, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T15_11_2 Q2.hfix15_11_2 Q2.hinj15_11_2
      Q2.hcardT15_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_11_2 i) (Q2.hfix15_11_2 i) _)
      colCert_15_11_0.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T15_11
      hfix15_11 hinj15_11 hcardT15_11
      (fun i => conj_mem_of_fixedPoints _ _ (T15_11 i) (hfix15_11 i) _)
      ⟨15, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T15_11_2 Q2.hfix15_11_2 Q2.hinj15_11_2
      Q2.hcardT15_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_11_2 i) (Q2.hfix15_11_2 i) _)
      colCert_15_11_1.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T15_11
      hfix15_11 hinj15_11 hcardT15_11
      (fun i => conj_mem_of_fixedPoints _ _ (T15_11 i) (hfix15_11 i) _)
      ⟨15, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T15_11_2 Q2.hfix15_11_2 Q2.hinj15_11_2
      Q2.hcardT15_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_11_2 i) (Q2.hfix15_11_2 i) _)
      colCert_15_11_2.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T15_11
      hfix15_11 hinj15_11 hcardT15_11
      (fun i => conj_mem_of_fixedPoints _ _ (T15_11 i) (hfix15_11 i) _)
      ⟨15, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T15_11_2 Q2.hfix15_11_2 Q2.hinj15_11_2
      Q2.hcardT15_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_11_2 i) (Q2.hfix15_11_2 i) _)
      colCert_15_11_3.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T15_11
      hfix15_11 hinj15_11 hcardT15_11
      (fun i => conj_mem_of_fixedPoints _ _ (T15_11 i) (hfix15_11 i) _)
      ⟨15, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T15_11_2 Q2.hfix15_11_2 Q2.hinj15_11_2
      Q2.hcardT15_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_11_2 i) (Q2.hfix15_11_2 i) _)
      colCert_15_11_4.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_0 (hp : 0 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 0 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 0 (transLenTr ⟨15, by decide⟩ 0 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 0 (transLenTr ⟨15, by decide⟩ 0 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 0 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_0.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_1 (hp : 1 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 1 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 1 (transLenTr ⟨15, by decide⟩ 1 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 1 (transLenTr ⟨15, by decide⟩ 1 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 1 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_1.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_2 (hp : 2 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 2 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 2 (transLenTr ⟨15, by decide⟩ 2 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 2 (transLenTr ⟨15, by decide⟩ 2 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 2 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_2.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_3 (hp : 3 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 3 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 3 (transLenTr ⟨15, by decide⟩ 3 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 3 (transLenTr ⟨15, by decide⟩ 3 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 3 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_3.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_4 (hp : 4 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 4 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 4 (transLenTr ⟨15, by decide⟩ 4 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 4 (transLenTr ⟨15, by decide⟩ 4 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 4 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_4.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_5 (hp : 5 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 5 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 5 (transLenTr ⟨15, by decide⟩ 5 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 5 (transLenTr ⟨15, by decide⟩ 5 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 5 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_5.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_6 (hp : 6 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 6 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 6 (transLenTr ⟨15, by decide⟩ 6 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 6 (transLenTr ⟨15, by decide⟩ 6 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 6 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_6.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_7 (hp : 7 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 7 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 7 (transLenTr ⟨15, by decide⟩ 7 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 7 (transLenTr ⟨15, by decide⟩ 7 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 7 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_7.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_8 (hp : 8 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 8 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 8 (transLenTr ⟨15, by decide⟩ 8 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 8 (transLenTr ⟨15, by decide⟩ 8 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 8 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_8.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_9 (hp : 9 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 9 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 9 (transLenTr ⟨15, by decide⟩ 9 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 9 (transLenTr ⟨15, by decide⟩ 9 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 9 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_9.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_10 (hp : 10 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 10 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 10 (transLenTr ⟨15, by decide⟩ 10 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 10 (transLenTr ⟨15, by decide⟩ 10 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 10 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_10.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_11 (hp : 11 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 11 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 11 (transLenTr ⟨15, by decide⟩ 11 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 11 (transLenTr ⟨15, by decide⟩ 11 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 11 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_11.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_12 (hp : 12 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 12 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 12 (transLenTr ⟨15, by decide⟩ 12 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 12 (transLenTr ⟨15, by decide⟩ 12 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 12 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_12.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_13 (hp : 13 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 13 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 13 (transLenTr ⟨15, by decide⟩ 13 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 13 (transLenTr ⟨15, by decide⟩ 13 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 13 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_13.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_14 (hp : 14 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 14 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 14 (transLenTr ⟨15, by decide⟩ 14 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 14 (transLenTr ⟨15, by decide⟩ 14 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 14 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_14.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_15 (hp : 15 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 15 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 15 (transLenTr ⟨15, by decide⟩ 15 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 15 (transLenTr ⟨15, by decide⟩ 15 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 15 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_15.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_16 (hp : 16 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 16 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 16 (transLenTr ⟨15, by decide⟩ 16 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 16 (transLenTr ⟨15, by decide⟩ 16 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 16 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_16.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_17 (hp : 17 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 17 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 17 (transLenTr ⟨15, by decide⟩ 17 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 17 (transLenTr ⟨15, by decide⟩ 17 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 17 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_17.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_18 (hp : 18 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 18 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 18 (transLenTr ⟨15, by decide⟩ 18 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 18 (transLenTr ⟨15, by decide⟩ 18 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 18 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_18.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_19 (hp : 19 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 19 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 19 (transLenTr ⟨15, by decide⟩ 19 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 19 (transLenTr ⟨15, by decide⟩ 19 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 19 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_19.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_20 (hp : 20 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 20 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 20 (transLenTr ⟨15, by decide⟩ 20 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 20 (transLenTr ⟨15, by decide⟩ 20 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 20 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_20.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_21 (hp : 21 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 21 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 21 (transLenTr ⟨15, by decide⟩ 21 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 21 (transLenTr ⟨15, by decide⟩ 21 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 21 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_21.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_22 (hp : 22 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 22 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 22 (transLenTr ⟨15, by decide⟩ 22 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 22 (transLenTr ⟨15, by decide⟩ 22 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 22 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_22.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_23 (hp : 23 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 23 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 23 (transLenTr ⟨15, by decide⟩ 23 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 23 (transLenTr ⟨15, by decide⟩ 23 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 23 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_23.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_15_15_24 (hp : 24 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 15 []).length)
    (hq : (normIsRep.getD 15 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 24 hp)
        (rowE2 (⟨15, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 24 (transLenTr ⟨15, by decide⟩ 24 hp))
        (rowE1 (⟨15, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨15, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨15, by decide⟩ (listedAt ⟨15, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 24 (transLenTr ⟨15, by decide⟩ 24 hp)) T15_15
      hfix15_15 hinj15_15 hcardT15_15
      (fun i => conj_mem_of_fixedPoints _ _ (T15_15 i) (hfix15_15 i) _)
      ⟨15, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨15, by decide⟩ (Q2.listedAt ⟨15, by decide⟩
        (alnCheck_rep ⟨15, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 24 hp) Q2.T15_15_2 Q2.hfix15_15_2 Q2.hinj15_15_2
      Q2.hcardT15_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T15_15_2 i) (Q2.hfix15_15_2 i) _)
      colCert_15_15_24.hD ?_).symm
  rw [alnId_15 j hj]


theorem leaf_16_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T16_2
      hfix16_2 hinj16_2 hcardT16_2
      (fun i => conj_mem_of_fixedPoints _ _ (T16_2 i) (hfix16_2 i) _)
      ⟨16, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T16_2_2 Q2.hfix16_2_2 Q2.hinj16_2_2
      Q2.hcardT16_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_2_2 i) (Q2.hfix16_2_2 i) _)
      colCert_16_2_0.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T16_2
      hfix16_2 hinj16_2 hcardT16_2
      (fun i => conj_mem_of_fixedPoints _ _ (T16_2 i) (hfix16_2 i) _)
      ⟨16, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T16_2_2 Q2.hfix16_2_2 Q2.hinj16_2_2
      Q2.hcardT16_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_2_2 i) (Q2.hfix16_2_2 i) _)
      colCert_16_2_1.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T16_2
      hfix16_2 hinj16_2 hcardT16_2
      (fun i => conj_mem_of_fixedPoints _ _ (T16_2 i) (hfix16_2 i) _)
      ⟨16, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T16_2_2 Q2.hfix16_2_2 Q2.hinj16_2_2
      Q2.hcardT16_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_2_2 i) (Q2.hfix16_2_2 i) _)
      colCert_16_2_2.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T16_2
      hfix16_2 hinj16_2 hcardT16_2
      (fun i => conj_mem_of_fixedPoints _ _ (T16_2 i) (hfix16_2 i) _)
      ⟨16, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T16_2_2 Q2.hfix16_2_2 Q2.hinj16_2_2
      Q2.hcardT16_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_2_2 i) (Q2.hfix16_2_2 i) _)
      colCert_16_2_3.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T16_2
      hfix16_2 hinj16_2 hcardT16_2
      (fun i => conj_mem_of_fixedPoints _ _ (T16_2 i) (hfix16_2 i) _)
      ⟨16, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T16_2_2 Q2.hfix16_2_2 Q2.hinj16_2_2
      Q2.hcardT16_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_2_2 i) (Q2.hfix16_2_2 i) _)
      colCert_16_2_4.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T16_3
      hfix16_3 hinj16_3 hcardT16_3
      (fun i => conj_mem_of_fixedPoints _ _ (T16_3 i) (hfix16_3 i) _)
      ⟨16, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T16_3_2 Q2.hfix16_3_2 Q2.hinj16_3_2
      Q2.hcardT16_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_3_2 i) (Q2.hfix16_3_2 i) _)
      colCert_16_3_0.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T16_3
      hfix16_3 hinj16_3 hcardT16_3
      (fun i => conj_mem_of_fixedPoints _ _ (T16_3 i) (hfix16_3 i) _)
      ⟨16, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T16_3_2 Q2.hfix16_3_2 Q2.hinj16_3_2
      Q2.hcardT16_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_3_2 i) (Q2.hfix16_3_2 i) _)
      colCert_16_3_1.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T16_3
      hfix16_3 hinj16_3 hcardT16_3
      (fun i => conj_mem_of_fixedPoints _ _ (T16_3 i) (hfix16_3 i) _)
      ⟨16, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T16_3_2 Q2.hfix16_3_2 Q2.hinj16_3_2
      Q2.hcardT16_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_3_2 i) (Q2.hfix16_3_2 i) _)
      colCert_16_3_2.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T16_3
      hfix16_3 hinj16_3 hcardT16_3
      (fun i => conj_mem_of_fixedPoints _ _ (T16_3 i) (hfix16_3 i) _)
      ⟨16, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T16_3_2 Q2.hfix16_3_2 Q2.hinj16_3_2
      Q2.hcardT16_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_3_2 i) (Q2.hfix16_3_2 i) _)
      colCert_16_3_3.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T16_3
      hfix16_3 hinj16_3 hcardT16_3
      (fun i => conj_mem_of_fixedPoints _ _ (T16_3 i) (hfix16_3 i) _)
      ⟨16, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T16_3_2 Q2.hfix16_3_2 Q2.hinj16_3_2
      Q2.hcardT16_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_3_2 i) (Q2.hfix16_3_2 i) _)
      colCert_16_3_4.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T16_4
      hfix16_4 hinj16_4 hcardT16_4
      (fun i => conj_mem_of_fixedPoints _ _ (T16_4 i) (hfix16_4 i) _)
      ⟨16, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T16_4_2 Q2.hfix16_4_2 Q2.hinj16_4_2
      Q2.hcardT16_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_4_2 i) (Q2.hfix16_4_2 i) _)
      colCert_16_4_0.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T16_4
      hfix16_4 hinj16_4 hcardT16_4
      (fun i => conj_mem_of_fixedPoints _ _ (T16_4 i) (hfix16_4 i) _)
      ⟨16, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T16_4_2 Q2.hfix16_4_2 Q2.hinj16_4_2
      Q2.hcardT16_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_4_2 i) (Q2.hfix16_4_2 i) _)
      colCert_16_4_1.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T16_4
      hfix16_4 hinj16_4 hcardT16_4
      (fun i => conj_mem_of_fixedPoints _ _ (T16_4 i) (hfix16_4 i) _)
      ⟨16, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T16_4_2 Q2.hfix16_4_2 Q2.hinj16_4_2
      Q2.hcardT16_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_4_2 i) (Q2.hfix16_4_2 i) _)
      colCert_16_4_2.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T16_4
      hfix16_4 hinj16_4 hcardT16_4
      (fun i => conj_mem_of_fixedPoints _ _ (T16_4 i) (hfix16_4 i) _)
      ⟨16, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T16_4_2 Q2.hfix16_4_2 Q2.hinj16_4_2
      Q2.hcardT16_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_4_2 i) (Q2.hfix16_4_2 i) _)
      colCert_16_4_3.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T16_4
      hfix16_4 hinj16_4 hcardT16_4
      (fun i => conj_mem_of_fixedPoints _ _ (T16_4 i) (hfix16_4 i) _)
      ⟨16, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T16_4_2 Q2.hfix16_4_2 Q2.hinj16_4_2
      Q2.hcardT16_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_4_2 i) (Q2.hfix16_4_2 i) _)
      colCert_16_4_4.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T16_5
      hfix16_5 hinj16_5 hcardT16_5
      (fun i => conj_mem_of_fixedPoints _ _ (T16_5 i) (hfix16_5 i) _)
      ⟨16, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T16_5_2 Q2.hfix16_5_2 Q2.hinj16_5_2
      Q2.hcardT16_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_5_2 i) (Q2.hfix16_5_2 i) _)
      colCert_16_5_0.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T16_5
      hfix16_5 hinj16_5 hcardT16_5
      (fun i => conj_mem_of_fixedPoints _ _ (T16_5 i) (hfix16_5 i) _)
      ⟨16, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T16_5_2 Q2.hfix16_5_2 Q2.hinj16_5_2
      Q2.hcardT16_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_5_2 i) (Q2.hfix16_5_2 i) _)
      colCert_16_5_1.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T16_5
      hfix16_5 hinj16_5 hcardT16_5
      (fun i => conj_mem_of_fixedPoints _ _ (T16_5 i) (hfix16_5 i) _)
      ⟨16, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T16_5_2 Q2.hfix16_5_2 Q2.hinj16_5_2
      Q2.hcardT16_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_5_2 i) (Q2.hfix16_5_2 i) _)
      colCert_16_5_2.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T16_5
      hfix16_5 hinj16_5 hcardT16_5
      (fun i => conj_mem_of_fixedPoints _ _ (T16_5 i) (hfix16_5 i) _)
      ⟨16, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T16_5_2 Q2.hfix16_5_2 Q2.hinj16_5_2
      Q2.hcardT16_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_5_2 i) (Q2.hfix16_5_2 i) _)
      colCert_16_5_3.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T16_5
      hfix16_5 hinj16_5 hcardT16_5
      (fun i => conj_mem_of_fixedPoints _ _ (T16_5 i) (hfix16_5 i) _)
      ⟨16, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T16_5_2 Q2.hfix16_5_2 Q2.hinj16_5_2
      Q2.hcardT16_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_5_2 i) (Q2.hfix16_5_2 i) _)
      colCert_16_5_4.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T16_9
      hfix16_9 hinj16_9 hcardT16_9
      (fun i => conj_mem_of_fixedPoints _ _ (T16_9 i) (hfix16_9 i) _)
      ⟨16, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T16_9_2 Q2.hfix16_9_2 Q2.hinj16_9_2
      Q2.hcardT16_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_9_2 i) (Q2.hfix16_9_2 i) _)
      colCert_16_9_0.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T16_9
      hfix16_9 hinj16_9 hcardT16_9
      (fun i => conj_mem_of_fixedPoints _ _ (T16_9 i) (hfix16_9 i) _)
      ⟨16, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T16_9_2 Q2.hfix16_9_2 Q2.hinj16_9_2
      Q2.hcardT16_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_9_2 i) (Q2.hfix16_9_2 i) _)
      colCert_16_9_1.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T16_9
      hfix16_9 hinj16_9 hcardT16_9
      (fun i => conj_mem_of_fixedPoints _ _ (T16_9 i) (hfix16_9 i) _)
      ⟨16, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T16_9_2 Q2.hfix16_9_2 Q2.hinj16_9_2
      Q2.hcardT16_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_9_2 i) (Q2.hfix16_9_2 i) _)
      colCert_16_9_2.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T16_9
      hfix16_9 hinj16_9 hcardT16_9
      (fun i => conj_mem_of_fixedPoints _ _ (T16_9 i) (hfix16_9 i) _)
      ⟨16, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T16_9_2 Q2.hfix16_9_2 Q2.hinj16_9_2
      Q2.hcardT16_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_9_2 i) (Q2.hfix16_9_2 i) _)
      colCert_16_9_3.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T16_9
      hfix16_9 hinj16_9 hcardT16_9
      (fun i => conj_mem_of_fixedPoints _ _ (T16_9 i) (hfix16_9 i) _)
      ⟨16, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T16_9_2 Q2.hfix16_9_2 Q2.hinj16_9_2
      Q2.hcardT16_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_9_2 i) (Q2.hfix16_9_2 i) _)
      colCert_16_9_4.hD ?_).symm
  rw [alnId_16 j hj]


end LeanDring.P5Presentation
