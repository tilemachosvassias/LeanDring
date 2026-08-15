/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C031
import LeanDring.P5.Data.ColCdd.C032
import LeanDring.P5.Data.ColCdd.C033
import LeanDring.P5.Data.ColRestCheap.C128
import LeanDring.P5.Data.ColRestCheap.C129
import LeanDring.P5.Data.ColRestCheap.C130
import LeanDring.P5.Data.ColRestCheap.C131
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C042

/-! # Stage-5 leaves, chunk 55 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_147_117_22 (hp : 22 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 22 (transLenTr ⟨117, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 22 (transLenTr ⟨117, by decide⟩ 22 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 22 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_23 (hp : 23 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 23 (transLenTr ⟨117, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 23 (transLenTr ⟨117, by decide⟩ 23 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 23 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_24 (hp : 24 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 24 (transLenTr ⟨117, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 24 (transLenTr ⟨117, by decide⟩ 24 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 24 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_25 (hp : 25 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 25 (transLenTr ⟨117, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 25 (transLenTr ⟨117, by decide⟩ 25 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 25 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_30 (hp : 30 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 30 (transLenTr ⟨117, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 30 (transLenTr ⟨117, by decide⟩ 30 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 30 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_35 (hp : 35 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 35 (transLenTr ⟨117, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 35 (transLenTr ⟨117, by decide⟩ 35 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 35 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_40 (hp : 40 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 40 (transLenTr ⟨117, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 40 (transLenTr ⟨117, by decide⟩ 40 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 40 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_45 (hp : 45 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 45 (transLenTr ⟨117, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 45 (transLenTr ⟨117, by decide⟩ 45 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 45 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      colCert_147_117_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_117_50 (hp : 50 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 50 (transLenTr ⟨117, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 50 (transLenTr ⟨117, by decide⟩ 50 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 50 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 50 (transLenTr ⟨117, by decide⟩ 50 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_50.D1 (m := 1) from colCertDiv_147_117_50.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 50 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_50.D2 (m := 1) from colCertDiv_147_117_50.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_50_match


theorem leaf_147_117_55 (hp : 55 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 55 (transLenTr ⟨117, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 55 (transLenTr ⟨117, by decide⟩ 55 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 55 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 55 (transLenTr ⟨117, by decide⟩ 55 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_55.D1 (m := 1) from colCertDiv_147_117_55.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 55 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_55.D2 (m := 1) from colCertDiv_147_117_55.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_55_match


theorem leaf_147_117_60 (hp : 60 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 60 (transLenTr ⟨117, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 60 (transLenTr ⟨117, by decide⟩ 60 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 60 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 60 (transLenTr ⟨117, by decide⟩ 60 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_60.D1 (m := 1) from colCertDiv_147_117_60.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 60 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_60.D2 (m := 1) from colCertDiv_147_117_60.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_60_match


theorem leaf_147_117_65 (hp : 65 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 65 (transLenTr ⟨117, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 65 (transLenTr ⟨117, by decide⟩ 65 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 65 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 65 (transLenTr ⟨117, by decide⟩ 65 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_65.D1 (m := 1) from colCertDiv_147_117_65.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 65 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_65.D2 (m := 1) from colCertDiv_147_117_65.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_65_match


theorem leaf_147_117_70 (hp : 70 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 70 (transLenTr ⟨117, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 70 (transLenTr ⟨117, by decide⟩ 70 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 70 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 70 (transLenTr ⟨117, by decide⟩ 70 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_70.D1 (m := 1) from colCertDiv_147_117_70.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 70 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_70.D2 (m := 1) from colCertDiv_147_117_70.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_70_match


theorem leaf_147_117_75 (hp : 75 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 75 (transLenTr ⟨117, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 75 (transLenTr ⟨117, by decide⟩ 75 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 75 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 75 (transLenTr ⟨117, by decide⟩ 75 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_75.D1 (m := 1) from colCertDiv_147_117_75.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 75 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_75.D2 (m := 1) from colCertDiv_147_117_75.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_75_match


theorem leaf_147_117_80 (hp : 80 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 80 (transLenTr ⟨117, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 80 (transLenTr ⟨117, by decide⟩ 80 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 80 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 80 (transLenTr ⟨117, by decide⟩ 80 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_80.D1 (m := 1) from colCertDiv_147_117_80.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 80 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_80.D2 (m := 1) from colCertDiv_147_117_80.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_80_match


theorem leaf_147_117_85 (hp : 85 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 85 (transLenTr ⟨117, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 85 (transLenTr ⟨117, by decide⟩ 85 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 85 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 85 (transLenTr ⟨117, by decide⟩ 85 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_85.D1 (m := 1) from colCertDiv_147_117_85.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 85 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_85.D2 (m := 1) from colCertDiv_147_117_85.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_85_match


theorem leaf_147_117_90 (hp : 90 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 90 (transLenTr ⟨117, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 90 (transLenTr ⟨117, by decide⟩ 90 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 90 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 90 (transLenTr ⟨117, by decide⟩ 90 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_90.D1 (m := 1) from colCertDiv_147_117_90.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 90 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_90.D2 (m := 1) from colCertDiv_147_117_90.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_90_match


theorem leaf_147_117_95 (hp : 95 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 95 (transLenTr ⟨117, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 95 (transLenTr ⟨117, by decide⟩ 95 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 95 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 95 (transLenTr ⟨117, by decide⟩ 95 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_95.D1 (m := 1) from colCertDiv_147_117_95.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 95 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_95.D2 (m := 1) from colCertDiv_147_117_95.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_95_match


theorem leaf_147_117_100 (hp : 100 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 100 (transLenTr ⟨117, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 100 (transLenTr ⟨117, by decide⟩ 100 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 100 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 100 (transLenTr ⟨117, by decide⟩ 100 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_100.D1 (m := 1) from colCertDiv_147_117_100.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 100 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_100.D2 (m := 1) from colCertDiv_147_117_100.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_100_match


theorem leaf_147_117_105 (hp : 105 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 105 (transLenTr ⟨117, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 105 (transLenTr ⟨117, by decide⟩ 105 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 105 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 105 (transLenTr ⟨117, by decide⟩ 105 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_105.D1 (m := 1) from colCertDiv_147_117_105.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 105 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_105.D2 (m := 1) from colCertDiv_147_117_105.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_105_match


theorem leaf_147_117_110 (hp : 110 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 110 (transLenTr ⟨117, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 110 (transLenTr ⟨117, by decide⟩ 110 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 110 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 110 (transLenTr ⟨117, by decide⟩ 110 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_110.D1 (m := 1) from colCertDiv_147_117_110.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 110 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_110.D2 (m := 1) from colCertDiv_147_117_110.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_110_match


theorem leaf_147_117_115 (hp : 115 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 115 (transLenTr ⟨117, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 115 (transLenTr ⟨117, by decide⟩ 115 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 115 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 115 (transLenTr ⟨117, by decide⟩ 115 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_115.D1 (m := 1) from colCertDiv_147_117_115.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 115 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_115.D2 (m := 1) from colCertDiv_147_117_115.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_115_match


theorem leaf_147_117_120 (hp : 120 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 120 (transLenTr ⟨117, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 120 (transLenTr ⟨117, by decide⟩ 120 hp)) T147_117
      hfix147_117 hinj147_117 hcardT147_117
      (fun i => conj_mem_of_fixedPoints _ _ (T147_117 i) (hfix147_117 i) _)
      ⟨147, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 120 hp) Q2.T147_117_2 Q2.hfix147_117_2 Q2.hinj147_117_2
      Q2.hcardT147_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_117_2 i) (Q2.hfix147_117_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨117, by decide⟩ 120 (transLenTr ⟨117, by decide⟩ 120 hp) : ↥(reps ⟨117, by decide⟩)) : Coordinate 1)
        T147_117 = colFn colCertDiv_147_117_120.D1 (m := 1) from colCertDiv_147_117_120.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨117, by decide⟩ 120 hp : ↥(Q2.reps ⟨117, by decide⟩)) : Coordinate 2)
        Q2.T147_117_2 = colFn colCertDiv_147_117_120.D2 (m := 1) from colCertDiv_147_117_120.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_117_120_match


theorem leaf_147_118_0 (hp : 0 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 0 (transLenTr ⟨118, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 0 (transLenTr ⟨118, by decide⟩ 0 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 0 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_1 (hp : 1 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 1 (transLenTr ⟨118, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 1 (transLenTr ⟨118, by decide⟩ 1 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 1 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_2 (hp : 2 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 2 (transLenTr ⟨118, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 2 (transLenTr ⟨118, by decide⟩ 2 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 2 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_3 (hp : 3 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 3 (transLenTr ⟨118, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 3 (transLenTr ⟨118, by decide⟩ 3 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 3 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_4 (hp : 4 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 4 (transLenTr ⟨118, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 4 (transLenTr ⟨118, by decide⟩ 4 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 4 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_5 (hp : 5 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 5 (transLenTr ⟨118, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 5 (transLenTr ⟨118, by decide⟩ 5 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 5 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_6 (hp : 6 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 6 (transLenTr ⟨118, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 6 (transLenTr ⟨118, by decide⟩ 6 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 6 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_7 (hp : 7 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 7 (transLenTr ⟨118, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 7 (transLenTr ⟨118, by decide⟩ 7 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 7 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_8 (hp : 8 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 8 (transLenTr ⟨118, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 8 (transLenTr ⟨118, by decide⟩ 8 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 8 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_9 (hp : 9 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 9 (transLenTr ⟨118, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 9 (transLenTr ⟨118, by decide⟩ 9 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 9 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_10 (hp : 10 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 10 (transLenTr ⟨118, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 10 (transLenTr ⟨118, by decide⟩ 10 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 10 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_11 (hp : 11 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 11 (transLenTr ⟨118, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 11 (transLenTr ⟨118, by decide⟩ 11 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 11 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_12 (hp : 12 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 12 (transLenTr ⟨118, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 12 (transLenTr ⟨118, by decide⟩ 12 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 12 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_13 (hp : 13 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 13 (transLenTr ⟨118, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 13 (transLenTr ⟨118, by decide⟩ 13 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 13 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_14 (hp : 14 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 14 (transLenTr ⟨118, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 14 (transLenTr ⟨118, by decide⟩ 14 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 14 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_15 (hp : 15 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 15 (transLenTr ⟨118, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 15 (transLenTr ⟨118, by decide⟩ 15 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 15 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_16 (hp : 16 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 16 (transLenTr ⟨118, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 16 (transLenTr ⟨118, by decide⟩ 16 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 16 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_17 (hp : 17 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 17 (transLenTr ⟨118, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 17 (transLenTr ⟨118, by decide⟩ 17 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 17 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_18 (hp : 18 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 18 (transLenTr ⟨118, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 18 (transLenTr ⟨118, by decide⟩ 18 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 18 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_19 (hp : 19 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 19 (transLenTr ⟨118, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 19 (transLenTr ⟨118, by decide⟩ 19 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 19 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_20 (hp : 20 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 20 (transLenTr ⟨118, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 20 (transLenTr ⟨118, by decide⟩ 20 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 20 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_21 (hp : 21 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 21 (transLenTr ⟨118, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 21 (transLenTr ⟨118, by decide⟩ 21 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 21 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_22 (hp : 22 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 22 (transLenTr ⟨118, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 22 (transLenTr ⟨118, by decide⟩ 22 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 22 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_23 (hp : 23 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 23 (transLenTr ⟨118, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 23 (transLenTr ⟨118, by decide⟩ 23 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 23 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_24 (hp : 24 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 24 (transLenTr ⟨118, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 24 (transLenTr ⟨118, by decide⟩ 24 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 24 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_25 (hp : 25 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 25 (transLenTr ⟨118, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 25 (transLenTr ⟨118, by decide⟩ 25 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 25 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_30 (hp : 30 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 30 (transLenTr ⟨118, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 30 (transLenTr ⟨118, by decide⟩ 30 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 30 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_35 (hp : 35 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 35 (transLenTr ⟨118, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 35 (transLenTr ⟨118, by decide⟩ 35 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 35 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_40 (hp : 40 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 40 (transLenTr ⟨118, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 40 (transLenTr ⟨118, by decide⟩ 40 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 40 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_45 (hp : 45 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 45 (transLenTr ⟨118, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 45 (transLenTr ⟨118, by decide⟩ 45 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 45 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_50 (hp : 50 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 50 (transLenTr ⟨118, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 50 (transLenTr ⟨118, by decide⟩ 50 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 50 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_55 (hp : 55 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 55 (transLenTr ⟨118, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 55 (transLenTr ⟨118, by decide⟩ 55 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 55 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_55.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_60 (hp : 60 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 60 (transLenTr ⟨118, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 60 (transLenTr ⟨118, by decide⟩ 60 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 60 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_60.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_65 (hp : 65 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 65 (transLenTr ⟨118, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 65 (transLenTr ⟨118, by decide⟩ 65 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 65 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_65.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_70 (hp : 70 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 70 (transLenTr ⟨118, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 70 (transLenTr ⟨118, by decide⟩ 70 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 70 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      colCert_147_118_70.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_118_75 (hp : 75 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 75 (transLenTr ⟨118, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 75 (transLenTr ⟨118, by decide⟩ 75 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 75 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨118, by decide⟩ 75 (transLenTr ⟨118, by decide⟩ 75 hp) : ↥(reps ⟨118, by decide⟩)) : Coordinate 1)
        T147_118 = colFn colCertDiv_147_118_75.D1 (m := 1) from colCertDiv_147_118_75.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨118, by decide⟩ 75 hp : ↥(Q2.reps ⟨118, by decide⟩)) : Coordinate 2)
        Q2.T147_118_2 = colFn colCertDiv_147_118_75.D2 (m := 1) from colCertDiv_147_118_75.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_118_75_match


theorem leaf_147_118_80 (hp : 80 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 80 (transLenTr ⟨118, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 80 (transLenTr ⟨118, by decide⟩ 80 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 80 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨118, by decide⟩ 80 (transLenTr ⟨118, by decide⟩ 80 hp) : ↥(reps ⟨118, by decide⟩)) : Coordinate 1)
        T147_118 = colFn colCertDiv_147_118_80.D1 (m := 1) from colCertDiv_147_118_80.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨118, by decide⟩ 80 hp : ↥(Q2.reps ⟨118, by decide⟩)) : Coordinate 2)
        Q2.T147_118_2 = colFn colCertDiv_147_118_80.D2 (m := 1) from colCertDiv_147_118_80.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_118_80_match


theorem leaf_147_118_85 (hp : 85 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 85 (transLenTr ⟨118, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 85 (transLenTr ⟨118, by decide⟩ 85 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 85 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨118, by decide⟩ 85 (transLenTr ⟨118, by decide⟩ 85 hp) : ↥(reps ⟨118, by decide⟩)) : Coordinate 1)
        T147_118 = colFn colCertDiv_147_118_85.D1 (m := 1) from colCertDiv_147_118_85.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨118, by decide⟩ 85 hp : ↥(Q2.reps ⟨118, by decide⟩)) : Coordinate 2)
        Q2.T147_118_2 = colFn colCertDiv_147_118_85.D2 (m := 1) from colCertDiv_147_118_85.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_118_85_match


theorem leaf_147_118_90 (hp : 90 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 90 (transLenTr ⟨118, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 90 (transLenTr ⟨118, by decide⟩ 90 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 90 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨118, by decide⟩ 90 (transLenTr ⟨118, by decide⟩ 90 hp) : ↥(reps ⟨118, by decide⟩)) : Coordinate 1)
        T147_118 = colFn colCertDiv_147_118_90.D1 (m := 1) from colCertDiv_147_118_90.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨118, by decide⟩ 90 hp : ↥(Q2.reps ⟨118, by decide⟩)) : Coordinate 2)
        Q2.T147_118_2 = colFn colCertDiv_147_118_90.D2 (m := 1) from colCertDiv_147_118_90.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_118_90_match


theorem leaf_147_118_95 (hp : 95 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 95 (transLenTr ⟨118, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 95 (transLenTr ⟨118, by decide⟩ 95 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 95 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨118, by decide⟩ 95 (transLenTr ⟨118, by decide⟩ 95 hp) : ↥(reps ⟨118, by decide⟩)) : Coordinate 1)
        T147_118 = colFn colCertDiv_147_118_95.D1 (m := 1) from colCertDiv_147_118_95.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨118, by decide⟩ 95 hp : ↥(Q2.reps ⟨118, by decide⟩)) : Coordinate 2)
        Q2.T147_118_2 = colFn colCertDiv_147_118_95.D2 (m := 1) from colCertDiv_147_118_95.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_118_95_match


theorem leaf_147_118_100 (hp : 100 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 100 (transLenTr ⟨118, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 100 (transLenTr ⟨118, by decide⟩ 100 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 100 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨118, by decide⟩ 100 (transLenTr ⟨118, by decide⟩ 100 hp) : ↥(reps ⟨118, by decide⟩)) : Coordinate 1)
        T147_118 = colFn colCertDiv_147_118_100.D1 (m := 1) from colCertDiv_147_118_100.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨118, by decide⟩ 100 hp : ↥(Q2.reps ⟨118, by decide⟩)) : Coordinate 2)
        Q2.T147_118_2 = colFn colCertDiv_147_118_100.D2 (m := 1) from colCertDiv_147_118_100.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_118_100_match


theorem leaf_147_118_105 (hp : 105 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 105 (transLenTr ⟨118, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 105 (transLenTr ⟨118, by decide⟩ 105 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 105 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨118, by decide⟩ 105 (transLenTr ⟨118, by decide⟩ 105 hp) : ↥(reps ⟨118, by decide⟩)) : Coordinate 1)
        T147_118 = colFn colCertDiv_147_118_105.D1 (m := 1) from colCertDiv_147_118_105.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨118, by decide⟩ 105 hp : ↥(Q2.reps ⟨118, by decide⟩)) : Coordinate 2)
        Q2.T147_118_2 = colFn colCertDiv_147_118_105.D2 (m := 1) from colCertDiv_147_118_105.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_118_105_match


theorem leaf_147_118_110 (hp : 110 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 110 (transLenTr ⟨118, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 110 (transLenTr ⟨118, by decide⟩ 110 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 110 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨118, by decide⟩ 110 (transLenTr ⟨118, by decide⟩ 110 hp) : ↥(reps ⟨118, by decide⟩)) : Coordinate 1)
        T147_118 = colFn colCertDiv_147_118_110.D1 (m := 1) from colCertDiv_147_118_110.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨118, by decide⟩ 110 hp : ↥(Q2.reps ⟨118, by decide⟩)) : Coordinate 2)
        Q2.T147_118_2 = colFn colCertDiv_147_118_110.D2 (m := 1) from colCertDiv_147_118_110.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_118_110_match


theorem leaf_147_118_115 (hp : 115 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 115 (transLenTr ⟨118, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 115 (transLenTr ⟨118, by decide⟩ 115 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 115 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨118, by decide⟩ 115 (transLenTr ⟨118, by decide⟩ 115 hp) : ↥(reps ⟨118, by decide⟩)) : Coordinate 1)
        T147_118 = colFn colCertDiv_147_118_115.D1 (m := 1) from colCertDiv_147_118_115.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨118, by decide⟩ 115 hp : ↥(Q2.reps ⟨118, by decide⟩)) : Coordinate 2)
        Q2.T147_118_2 = colFn colCertDiv_147_118_115.D2 (m := 1) from colCertDiv_147_118_115.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_118_115_match


theorem leaf_147_118_120 (hp : 120 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 120 (transLenTr ⟨118, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 120 (transLenTr ⟨118, by decide⟩ 120 hp)) T147_118
      hfix147_118 hinj147_118 hcardT147_118
      (fun i => conj_mem_of_fixedPoints _ _ (T147_118 i) (hfix147_118 i) _)
      ⟨147, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 120 hp) Q2.T147_118_2 Q2.hfix147_118_2 Q2.hinj147_118_2
      Q2.hcardT147_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_118_2 i) (Q2.hfix147_118_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨118, by decide⟩ 120 (transLenTr ⟨118, by decide⟩ 120 hp) : ↥(reps ⟨118, by decide⟩)) : Coordinate 1)
        T147_118 = colFn colCertDiv_147_118_120.D1 (m := 1) from colCertDiv_147_118_120.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨118, by decide⟩ 120 hp : ↥(Q2.reps ⟨118, by decide⟩)) : Coordinate 2)
        Q2.T147_118_2 = colFn colCertDiv_147_118_120.D2 (m := 1) from colCertDiv_147_118_120.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_118_120_match


theorem leaf_147_119_0 (hp : 0 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 0 (transLenTr ⟨119, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 0 (transLenTr ⟨119, by decide⟩ 0 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 0 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_1 (hp : 1 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 1 (transLenTr ⟨119, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 1 (transLenTr ⟨119, by decide⟩ 1 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 1 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_2 (hp : 2 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 2 (transLenTr ⟨119, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 2 (transLenTr ⟨119, by decide⟩ 2 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 2 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_3 (hp : 3 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 3 (transLenTr ⟨119, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 3 (transLenTr ⟨119, by decide⟩ 3 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 3 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_4 (hp : 4 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 4 (transLenTr ⟨119, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 4 (transLenTr ⟨119, by decide⟩ 4 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 4 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_5 (hp : 5 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 5 (transLenTr ⟨119, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 5 (transLenTr ⟨119, by decide⟩ 5 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 5 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_6 (hp : 6 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 6 (transLenTr ⟨119, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 6 (transLenTr ⟨119, by decide⟩ 6 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 6 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_7 (hp : 7 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 7 (transLenTr ⟨119, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 7 (transLenTr ⟨119, by decide⟩ 7 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 7 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_8 (hp : 8 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 8 (transLenTr ⟨119, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 8 (transLenTr ⟨119, by decide⟩ 8 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 8 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_9 (hp : 9 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 9 (transLenTr ⟨119, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 9 (transLenTr ⟨119, by decide⟩ 9 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 9 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_10 (hp : 10 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 10 (transLenTr ⟨119, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 10 (transLenTr ⟨119, by decide⟩ 10 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 10 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_11 (hp : 11 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 11 (transLenTr ⟨119, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 11 (transLenTr ⟨119, by decide⟩ 11 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 11 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_12 (hp : 12 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 12 (transLenTr ⟨119, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 12 (transLenTr ⟨119, by decide⟩ 12 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 12 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_13 (hp : 13 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 13 (transLenTr ⟨119, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 13 (transLenTr ⟨119, by decide⟩ 13 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 13 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_14 (hp : 14 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 14 (transLenTr ⟨119, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 14 (transLenTr ⟨119, by decide⟩ 14 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 14 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_15 (hp : 15 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 15 (transLenTr ⟨119, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 15 (transLenTr ⟨119, by decide⟩ 15 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 15 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_16 (hp : 16 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 16 (transLenTr ⟨119, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 16 (transLenTr ⟨119, by decide⟩ 16 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 16 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_17 (hp : 17 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 17 (transLenTr ⟨119, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 17 (transLenTr ⟨119, by decide⟩ 17 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 17 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_18 (hp : 18 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 18 (transLenTr ⟨119, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 18 (transLenTr ⟨119, by decide⟩ 18 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 18 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_19 (hp : 19 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 19 (transLenTr ⟨119, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 19 (transLenTr ⟨119, by decide⟩ 19 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 19 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_20 (hp : 20 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 20 (transLenTr ⟨119, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 20 (transLenTr ⟨119, by decide⟩ 20 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 20 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_21 (hp : 21 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 21 (transLenTr ⟨119, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 21 (transLenTr ⟨119, by decide⟩ 21 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 21 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_22 (hp : 22 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 22 (transLenTr ⟨119, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 22 (transLenTr ⟨119, by decide⟩ 22 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 22 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_23 (hp : 23 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 23 (transLenTr ⟨119, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 23 (transLenTr ⟨119, by decide⟩ 23 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 23 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_24 (hp : 24 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 24 (transLenTr ⟨119, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 24 (transLenTr ⟨119, by decide⟩ 24 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 24 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_25 (hp : 25 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 25 (transLenTr ⟨119, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 25 (transLenTr ⟨119, by decide⟩ 25 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 25 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_30 (hp : 30 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 30 (transLenTr ⟨119, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 30 (transLenTr ⟨119, by decide⟩ 30 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 30 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_35 (hp : 35 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 35 (transLenTr ⟨119, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 35 (transLenTr ⟨119, by decide⟩ 35 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 35 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_40 (hp : 40 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 40 (transLenTr ⟨119, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 40 (transLenTr ⟨119, by decide⟩ 40 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 40 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_45 (hp : 45 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 45 (transLenTr ⟨119, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 45 (transLenTr ⟨119, by decide⟩ 45 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 45 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      colCert_147_119_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_119_50 (hp : 50 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 50 (transLenTr ⟨119, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 50 (transLenTr ⟨119, by decide⟩ 50 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 50 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 50 (transLenTr ⟨119, by decide⟩ 50 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_50.D1 (m := 1) from colCertDiv_147_119_50.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 50 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_50.D2 (m := 1) from colCertDiv_147_119_50.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_50_match


theorem leaf_147_119_55 (hp : 55 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 55 (transLenTr ⟨119, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 55 (transLenTr ⟨119, by decide⟩ 55 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 55 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 55 (transLenTr ⟨119, by decide⟩ 55 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_55.D1 (m := 1) from colCertDiv_147_119_55.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 55 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_55.D2 (m := 1) from colCertDiv_147_119_55.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_55_match


theorem leaf_147_119_60 (hp : 60 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 60 (transLenTr ⟨119, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 60 (transLenTr ⟨119, by decide⟩ 60 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 60 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 60 (transLenTr ⟨119, by decide⟩ 60 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_60.D1 (m := 1) from colCertDiv_147_119_60.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 60 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_60.D2 (m := 1) from colCertDiv_147_119_60.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_60_match


theorem leaf_147_119_65 (hp : 65 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 65 (transLenTr ⟨119, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 65 (transLenTr ⟨119, by decide⟩ 65 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 65 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 65 (transLenTr ⟨119, by decide⟩ 65 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_65.D1 (m := 1) from colCertDiv_147_119_65.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 65 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_65.D2 (m := 1) from colCertDiv_147_119_65.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_65_match


theorem leaf_147_119_70 (hp : 70 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 70 (transLenTr ⟨119, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 70 (transLenTr ⟨119, by decide⟩ 70 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 70 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 70 (transLenTr ⟨119, by decide⟩ 70 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_70.D1 (m := 1) from colCertDiv_147_119_70.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 70 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_70.D2 (m := 1) from colCertDiv_147_119_70.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_70_match


theorem leaf_147_119_75 (hp : 75 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 75 (transLenTr ⟨119, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 75 (transLenTr ⟨119, by decide⟩ 75 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 75 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 75 (transLenTr ⟨119, by decide⟩ 75 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_75.D1 (m := 1) from colCertDiv_147_119_75.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 75 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_75.D2 (m := 1) from colCertDiv_147_119_75.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_75_match


theorem leaf_147_119_80 (hp : 80 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 80 (transLenTr ⟨119, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 80 (transLenTr ⟨119, by decide⟩ 80 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 80 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 80 (transLenTr ⟨119, by decide⟩ 80 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_80.D1 (m := 1) from colCertDiv_147_119_80.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 80 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_80.D2 (m := 1) from colCertDiv_147_119_80.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_80_match


theorem leaf_147_119_85 (hp : 85 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 85 (transLenTr ⟨119, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 85 (transLenTr ⟨119, by decide⟩ 85 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 85 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 85 (transLenTr ⟨119, by decide⟩ 85 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_85.D1 (m := 1) from colCertDiv_147_119_85.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 85 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_85.D2 (m := 1) from colCertDiv_147_119_85.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_85_match


theorem leaf_147_119_90 (hp : 90 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 90 (transLenTr ⟨119, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 90 (transLenTr ⟨119, by decide⟩ 90 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 90 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 90 (transLenTr ⟨119, by decide⟩ 90 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_90.D1 (m := 1) from colCertDiv_147_119_90.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 90 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_90.D2 (m := 1) from colCertDiv_147_119_90.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_90_match


theorem leaf_147_119_95 (hp : 95 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 95 (transLenTr ⟨119, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 95 (transLenTr ⟨119, by decide⟩ 95 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 95 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 95 (transLenTr ⟨119, by decide⟩ 95 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_95.D1 (m := 1) from colCertDiv_147_119_95.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 95 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_95.D2 (m := 1) from colCertDiv_147_119_95.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_95_match


theorem leaf_147_119_100 (hp : 100 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 100 (transLenTr ⟨119, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 100 (transLenTr ⟨119, by decide⟩ 100 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 100 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 100 (transLenTr ⟨119, by decide⟩ 100 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_100.D1 (m := 1) from colCertDiv_147_119_100.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 100 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_100.D2 (m := 1) from colCertDiv_147_119_100.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_100_match


theorem leaf_147_119_105 (hp : 105 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 105 (transLenTr ⟨119, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 105 (transLenTr ⟨119, by decide⟩ 105 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 105 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 105 (transLenTr ⟨119, by decide⟩ 105 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_105.D1 (m := 1) from colCertDiv_147_119_105.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 105 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_105.D2 (m := 1) from colCertDiv_147_119_105.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_105_match


theorem leaf_147_119_110 (hp : 110 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 110 (transLenTr ⟨119, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 110 (transLenTr ⟨119, by decide⟩ 110 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 110 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 110 (transLenTr ⟨119, by decide⟩ 110 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_110.D1 (m := 1) from colCertDiv_147_119_110.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 110 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_110.D2 (m := 1) from colCertDiv_147_119_110.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_110_match


theorem leaf_147_119_115 (hp : 115 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 115 (transLenTr ⟨119, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 115 (transLenTr ⟨119, by decide⟩ 115 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 115 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 115 (transLenTr ⟨119, by decide⟩ 115 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_115.D1 (m := 1) from colCertDiv_147_119_115.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 115 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_115.D2 (m := 1) from colCertDiv_147_119_115.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_115_match


theorem leaf_147_119_120 (hp : 120 < (Q2.transData.getD 119 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ 120 (transLenTr ⟨119, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨119, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨119, by decide⟩ 120 (transLenTr ⟨119, by decide⟩ 120 hp)) T147_119
      hfix147_119 hinj147_119 hcardT147_119
      (fun i => conj_mem_of_fixedPoints _ _ (T147_119 i) (hfix147_119 i) _)
      ⟨147, by decide⟩ ⟨119, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨119, by decide⟩ 120 hp) Q2.T147_119_2 Q2.hfix147_119_2 Q2.hinj147_119_2
      Q2.hcardT147_119_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_119_2 i) (Q2.hfix147_119_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨119, by decide⟩ 120 (transLenTr ⟨119, by decide⟩ 120 hp) : ↥(reps ⟨119, by decide⟩)) : Coordinate 1)
        T147_119 = colFn colCertDiv_147_119_120.D1 (m := 1) from colCertDiv_147_119_120.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨119, by decide⟩ 120 hp : ↥(Q2.reps ⟨119, by decide⟩)) : Coordinate 2)
        Q2.T147_119_2 = colFn colCertDiv_147_119_120.D2 (m := 1) from colCertDiv_147_119_120.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_119_120_match


theorem leaf_147_120_0 (hp : 0 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 0 (transLenTr ⟨120, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 0 (transLenTr ⟨120, by decide⟩ 0 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 0 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_1 (hp : 1 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 1 (transLenTr ⟨120, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 1 (transLenTr ⟨120, by decide⟩ 1 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 1 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_2 (hp : 2 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 2 (transLenTr ⟨120, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 2 (transLenTr ⟨120, by decide⟩ 2 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 2 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_3 (hp : 3 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 3 (transLenTr ⟨120, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 3 (transLenTr ⟨120, by decide⟩ 3 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 3 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_4 (hp : 4 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 4 (transLenTr ⟨120, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 4 (transLenTr ⟨120, by decide⟩ 4 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 4 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_5 (hp : 5 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 5 (transLenTr ⟨120, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 5 (transLenTr ⟨120, by decide⟩ 5 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 5 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_6 (hp : 6 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 6 (transLenTr ⟨120, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 6 (transLenTr ⟨120, by decide⟩ 6 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 6 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_7 (hp : 7 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 7 (transLenTr ⟨120, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 7 (transLenTr ⟨120, by decide⟩ 7 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 7 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_8 (hp : 8 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 8 (transLenTr ⟨120, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 8 (transLenTr ⟨120, by decide⟩ 8 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 8 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_9 (hp : 9 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 9 (transLenTr ⟨120, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 9 (transLenTr ⟨120, by decide⟩ 9 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 9 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_10 (hp : 10 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 10 (transLenTr ⟨120, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 10 (transLenTr ⟨120, by decide⟩ 10 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 10 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_11 (hp : 11 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 11 (transLenTr ⟨120, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 11 (transLenTr ⟨120, by decide⟩ 11 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 11 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_12 (hp : 12 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 12 (transLenTr ⟨120, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 12 (transLenTr ⟨120, by decide⟩ 12 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 12 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_13 (hp : 13 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 13 (transLenTr ⟨120, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 13 (transLenTr ⟨120, by decide⟩ 13 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 13 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_14 (hp : 14 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 14 (transLenTr ⟨120, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 14 (transLenTr ⟨120, by decide⟩ 14 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 14 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_15 (hp : 15 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 15 (transLenTr ⟨120, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 15 (transLenTr ⟨120, by decide⟩ 15 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 15 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_16 (hp : 16 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 16 (transLenTr ⟨120, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 16 (transLenTr ⟨120, by decide⟩ 16 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 16 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_17 (hp : 17 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 17 (transLenTr ⟨120, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 17 (transLenTr ⟨120, by decide⟩ 17 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 17 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_18 (hp : 18 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 18 (transLenTr ⟨120, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 18 (transLenTr ⟨120, by decide⟩ 18 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 18 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_19 (hp : 19 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 19 (transLenTr ⟨120, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 19 (transLenTr ⟨120, by decide⟩ 19 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 19 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_20 (hp : 20 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 20 (transLenTr ⟨120, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 20 (transLenTr ⟨120, by decide⟩ 20 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 20 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_21 (hp : 21 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 21 (transLenTr ⟨120, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 21 (transLenTr ⟨120, by decide⟩ 21 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 21 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_22 (hp : 22 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 22 (transLenTr ⟨120, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 22 (transLenTr ⟨120, by decide⟩ 22 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 22 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_23 (hp : 23 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 23 (transLenTr ⟨120, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 23 (transLenTr ⟨120, by decide⟩ 23 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 23 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_24 (hp : 24 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 24 (transLenTr ⟨120, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 24 (transLenTr ⟨120, by decide⟩ 24 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 24 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_25 (hp : 25 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 25 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 25 (transLenTr ⟨120, by decide⟩ 25 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 25 (transLenTr ⟨120, by decide⟩ 25 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 25 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_25.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_30 (hp : 30 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 30 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 30 (transLenTr ⟨120, by decide⟩ 30 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 30 (transLenTr ⟨120, by decide⟩ 30 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 30 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_30.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_35 (hp : 35 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 35 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 35 (transLenTr ⟨120, by decide⟩ 35 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 35 (transLenTr ⟨120, by decide⟩ 35 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 35 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_35.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_40 (hp : 40 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 40 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 40 (transLenTr ⟨120, by decide⟩ 40 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 40 (transLenTr ⟨120, by decide⟩ 40 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 40 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_40.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_45 (hp : 45 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 45 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 45 (transLenTr ⟨120, by decide⟩ 45 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 45 (transLenTr ⟨120, by decide⟩ 45 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 45 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_45.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_50 (hp : 50 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 50 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 50 (transLenTr ⟨120, by decide⟩ 50 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 50 (transLenTr ⟨120, by decide⟩ 50 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 50 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_50.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_55 (hp : 55 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 55 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 55 (transLenTr ⟨120, by decide⟩ 55 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 55 (transLenTr ⟨120, by decide⟩ 55 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 55 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_55.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_60 (hp : 60 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 60 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 60 (transLenTr ⟨120, by decide⟩ 60 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 60 (transLenTr ⟨120, by decide⟩ 60 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 60 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_60.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_65 (hp : 65 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 65 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 65 (transLenTr ⟨120, by decide⟩ 65 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 65 (transLenTr ⟨120, by decide⟩ 65 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 65 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_65.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_70 (hp : 70 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 70 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 70 (transLenTr ⟨120, by decide⟩ 70 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 70 (transLenTr ⟨120, by decide⟩ 70 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 70 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_70.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_75 (hp : 75 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 75 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 75 (transLenTr ⟨120, by decide⟩ 75 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 75 (transLenTr ⟨120, by decide⟩ 75 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 75 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_75.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_80 (hp : 80 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 80 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 80 (transLenTr ⟨120, by decide⟩ 80 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 80 (transLenTr ⟨120, by decide⟩ 80 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 80 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_80.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_85 (hp : 85 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 85 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 85 (transLenTr ⟨120, by decide⟩ 85 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 85 (transLenTr ⟨120, by decide⟩ 85 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 85 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_85.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_90 (hp : 90 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 90 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 90 (transLenTr ⟨120, by decide⟩ 90 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 90 (transLenTr ⟨120, by decide⟩ 90 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 90 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_90.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_95 (hp : 95 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 95 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 95 (transLenTr ⟨120, by decide⟩ 95 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 95 (transLenTr ⟨120, by decide⟩ 95 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 95 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_95.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_100 (hp : 100 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 100 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 100 (transLenTr ⟨120, by decide⟩ 100 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 100 (transLenTr ⟨120, by decide⟩ 100 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 100 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_100.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_105 (hp : 105 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 105 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 105 (transLenTr ⟨120, by decide⟩ 105 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 105 (transLenTr ⟨120, by decide⟩ 105 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 105 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_105.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_110 (hp : 110 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 110 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 110 (transLenTr ⟨120, by decide⟩ 110 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 110 (transLenTr ⟨120, by decide⟩ 110 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 110 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_110.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_115 (hp : 115 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 115 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 115 (transLenTr ⟨120, by decide⟩ 115 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 115 (transLenTr ⟨120, by decide⟩ 115 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 115 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_115.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_120_120 (hp : 120 < (Q2.transData.getD 120 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ 120 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ 120 (transLenTr ⟨120, by decide⟩ 120 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨120, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨120, by decide⟩ 120 (transLenTr ⟨120, by decide⟩ 120 hp)) T147_120
      hfix147_120 hinj147_120 hcardT147_120
      (fun i => conj_mem_of_fixedPoints _ _ (T147_120 i) (hfix147_120 i) _)
      ⟨147, by decide⟩ ⟨120, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨120, by decide⟩ 120 hp) Q2.T147_120_2 Q2.hfix147_120_2 Q2.hinj147_120_2
      Q2.hcardT147_120_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_120_2 i) (Q2.hfix147_120_2 i) _)
      colCert_147_120_120.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_0 (hp : 0 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 0 (transLenTr ⟨121, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 0 (transLenTr ⟨121, by decide⟩ 0 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 0 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_1 (hp : 1 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 1 (transLenTr ⟨121, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 1 (transLenTr ⟨121, by decide⟩ 1 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 1 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_2 (hp : 2 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 2 (transLenTr ⟨121, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 2 (transLenTr ⟨121, by decide⟩ 2 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 2 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_3 (hp : 3 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 3 (transLenTr ⟨121, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 3 (transLenTr ⟨121, by decide⟩ 3 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 3 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_4 (hp : 4 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 4 (transLenTr ⟨121, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 4 (transLenTr ⟨121, by decide⟩ 4 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 4 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_5 (hp : 5 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 5 (transLenTr ⟨121, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 5 (transLenTr ⟨121, by decide⟩ 5 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 5 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_6 (hp : 6 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 6 (transLenTr ⟨121, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 6 (transLenTr ⟨121, by decide⟩ 6 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 6 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_7 (hp : 7 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 7 (transLenTr ⟨121, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 7 (transLenTr ⟨121, by decide⟩ 7 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 7 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_8 (hp : 8 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 8 (transLenTr ⟨121, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 8 (transLenTr ⟨121, by decide⟩ 8 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 8 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_9 (hp : 9 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 9 (transLenTr ⟨121, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 9 (transLenTr ⟨121, by decide⟩ 9 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 9 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_10 (hp : 10 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 10 (transLenTr ⟨121, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 10 (transLenTr ⟨121, by decide⟩ 10 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 10 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_11 (hp : 11 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 11 (transLenTr ⟨121, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 11 (transLenTr ⟨121, by decide⟩ 11 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 11 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_12 (hp : 12 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 12 (transLenTr ⟨121, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 12 (transLenTr ⟨121, by decide⟩ 12 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 12 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_13 (hp : 13 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 13 (transLenTr ⟨121, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 13 (transLenTr ⟨121, by decide⟩ 13 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 13 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_14 (hp : 14 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 14 (transLenTr ⟨121, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 14 (transLenTr ⟨121, by decide⟩ 14 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 14 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_15 (hp : 15 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 15 (transLenTr ⟨121, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 15 (transLenTr ⟨121, by decide⟩ 15 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 15 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_16 (hp : 16 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 16 (transLenTr ⟨121, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 16 (transLenTr ⟨121, by decide⟩ 16 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 16 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_17 (hp : 17 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 17 (transLenTr ⟨121, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 17 (transLenTr ⟨121, by decide⟩ 17 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 17 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_18 (hp : 18 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 18 (transLenTr ⟨121, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 18 (transLenTr ⟨121, by decide⟩ 18 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 18 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_19 (hp : 19 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 19 (transLenTr ⟨121, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 19 (transLenTr ⟨121, by decide⟩ 19 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 19 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_20 (hp : 20 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 20 (transLenTr ⟨121, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 20 (transLenTr ⟨121, by decide⟩ 20 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 20 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_21 (hp : 21 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 21 (transLenTr ⟨121, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 21 (transLenTr ⟨121, by decide⟩ 21 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 21 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_22 (hp : 22 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 22 (transLenTr ⟨121, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 22 (transLenTr ⟨121, by decide⟩ 22 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 22 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_23 (hp : 23 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 23 (transLenTr ⟨121, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 23 (transLenTr ⟨121, by decide⟩ 23 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 23 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_121_24 (hp : 24 < (Q2.transData.getD 121 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ 24 (transLenTr ⟨121, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨121, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨121, by decide⟩ 24 (transLenTr ⟨121, by decide⟩ 24 hp)) T147_121
      hfix147_121 hinj147_121 hcardT147_121
      (fun i => conj_mem_of_fixedPoints _ _ (T147_121 i) (hfix147_121 i) _)
      ⟨147, by decide⟩ ⟨121, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨121, by decide⟩ 24 hp) Q2.T147_121_2 Q2.hfix147_121_2 Q2.hinj147_121_2
      Q2.hcardT147_121_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_121_2 i) (Q2.hfix147_121_2 i) _)
      colCert_147_121_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_122_0 (hp : 0 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 0 (transLenTr ⟨122, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 0 (transLenTr ⟨122, by decide⟩ 0 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 0 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      colCert_147_122_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_122_1 (hp : 1 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 1 (transLenTr ⟨122, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 1 (transLenTr ⟨122, by decide⟩ 1 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 1 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 1 (transLenTr ⟨122, by decide⟩ 1 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_1.D1 (m := 1) from colCertDiv_147_122_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 1 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_1.D2 (m := 1) from colCertDiv_147_122_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_1_match


theorem leaf_147_122_2 (hp : 2 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 2 (transLenTr ⟨122, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 2 (transLenTr ⟨122, by decide⟩ 2 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 2 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 2 (transLenTr ⟨122, by decide⟩ 2 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_2.D1 (m := 1) from colCertDiv_147_122_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 2 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_2.D2 (m := 1) from colCertDiv_147_122_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_2_match


theorem leaf_147_122_3 (hp : 3 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 3 (transLenTr ⟨122, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 3 (transLenTr ⟨122, by decide⟩ 3 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 3 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 3 (transLenTr ⟨122, by decide⟩ 3 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_3.D1 (m := 1) from colCertDiv_147_122_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 3 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_3.D2 (m := 1) from colCertDiv_147_122_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_3_match


theorem leaf_147_122_4 (hp : 4 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 4 (transLenTr ⟨122, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 4 (transLenTr ⟨122, by decide⟩ 4 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 4 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 4 (transLenTr ⟨122, by decide⟩ 4 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_4.D1 (m := 1) from colCertDiv_147_122_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 4 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_4.D2 (m := 1) from colCertDiv_147_122_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_4_match


theorem leaf_147_122_5 (hp : 5 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 5 (transLenTr ⟨122, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 5 (transLenTr ⟨122, by decide⟩ 5 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 5 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 5 (transLenTr ⟨122, by decide⟩ 5 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_5.D1 (m := 1) from colCertDiv_147_122_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 5 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_5.D2 (m := 1) from colCertDiv_147_122_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_5_match


theorem leaf_147_122_6 (hp : 6 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 6 (transLenTr ⟨122, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 6 (transLenTr ⟨122, by decide⟩ 6 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 6 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 6 (transLenTr ⟨122, by decide⟩ 6 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_6.D1 (m := 1) from colCertDiv_147_122_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 6 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_6.D2 (m := 1) from colCertDiv_147_122_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_6_match


theorem leaf_147_122_7 (hp : 7 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 7 (transLenTr ⟨122, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 7 (transLenTr ⟨122, by decide⟩ 7 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 7 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 7 (transLenTr ⟨122, by decide⟩ 7 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_7.D1 (m := 1) from colCertDiv_147_122_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 7 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_7.D2 (m := 1) from colCertDiv_147_122_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_7_match


theorem leaf_147_122_8 (hp : 8 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 8 (transLenTr ⟨122, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 8 (transLenTr ⟨122, by decide⟩ 8 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 8 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 8 (transLenTr ⟨122, by decide⟩ 8 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_8.D1 (m := 1) from colCertDiv_147_122_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 8 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_8.D2 (m := 1) from colCertDiv_147_122_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_8_match


theorem leaf_147_122_9 (hp : 9 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 9 (transLenTr ⟨122, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 9 (transLenTr ⟨122, by decide⟩ 9 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 9 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      colCert_147_122_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_122_10 (hp : 10 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 10 (transLenTr ⟨122, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 10 (transLenTr ⟨122, by decide⟩ 10 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 10 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 10 (transLenTr ⟨122, by decide⟩ 10 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_10.D1 (m := 1) from colCertDiv_147_122_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 10 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_10.D2 (m := 1) from colCertDiv_147_122_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_10_match


theorem leaf_147_122_11 (hp : 11 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 11 (transLenTr ⟨122, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 11 (transLenTr ⟨122, by decide⟩ 11 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 11 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 11 (transLenTr ⟨122, by decide⟩ 11 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_11.D1 (m := 1) from colCertDiv_147_122_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 11 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_11.D2 (m := 1) from colCertDiv_147_122_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_11_match


theorem leaf_147_122_12 (hp : 12 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 12 (transLenTr ⟨122, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 12 (transLenTr ⟨122, by decide⟩ 12 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 12 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 12 (transLenTr ⟨122, by decide⟩ 12 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_12.D1 (m := 1) from colCertDiv_147_122_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 12 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_12.D2 (m := 1) from colCertDiv_147_122_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_12_match


theorem leaf_147_122_13 (hp : 13 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 13 (transLenTr ⟨122, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 13 (transLenTr ⟨122, by decide⟩ 13 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 13 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      colCert_147_122_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_122_14 (hp : 14 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 14 (transLenTr ⟨122, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 14 (transLenTr ⟨122, by decide⟩ 14 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 14 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 14 (transLenTr ⟨122, by decide⟩ 14 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_14.D1 (m := 1) from colCertDiv_147_122_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 14 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_14.D2 (m := 1) from colCertDiv_147_122_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_14_match


theorem leaf_147_122_15 (hp : 15 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 15 (transLenTr ⟨122, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 15 (transLenTr ⟨122, by decide⟩ 15 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 15 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 15 (transLenTr ⟨122, by decide⟩ 15 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_15.D1 (m := 1) from colCertDiv_147_122_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 15 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_15.D2 (m := 1) from colCertDiv_147_122_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_15_match


theorem leaf_147_122_16 (hp : 16 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 16 (transLenTr ⟨122, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 16 (transLenTr ⟨122, by decide⟩ 16 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 16 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 16 (transLenTr ⟨122, by decide⟩ 16 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_16.D1 (m := 1) from colCertDiv_147_122_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 16 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_16.D2 (m := 1) from colCertDiv_147_122_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_16_match


theorem leaf_147_122_17 (hp : 17 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 17 (transLenTr ⟨122, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 17 (transLenTr ⟨122, by decide⟩ 17 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 17 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      colCert_147_122_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_122_18 (hp : 18 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 18 (transLenTr ⟨122, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 18 (transLenTr ⟨122, by decide⟩ 18 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 18 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 18 (transLenTr ⟨122, by decide⟩ 18 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_18.D1 (m := 1) from colCertDiv_147_122_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 18 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_18.D2 (m := 1) from colCertDiv_147_122_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_18_match


theorem leaf_147_122_19 (hp : 19 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 19 (transLenTr ⟨122, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 19 (transLenTr ⟨122, by decide⟩ 19 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 19 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 19 (transLenTr ⟨122, by decide⟩ 19 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_19.D1 (m := 1) from colCertDiv_147_122_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 19 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_19.D2 (m := 1) from colCertDiv_147_122_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_19_match


theorem leaf_147_122_20 (hp : 20 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 20 (transLenTr ⟨122, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 20 (transLenTr ⟨122, by decide⟩ 20 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 20 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 20 (transLenTr ⟨122, by decide⟩ 20 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_20.D1 (m := 1) from colCertDiv_147_122_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 20 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_20.D2 (m := 1) from colCertDiv_147_122_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_20_match


theorem leaf_147_122_21 (hp : 21 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 21 (transLenTr ⟨122, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 21 (transLenTr ⟨122, by decide⟩ 21 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 21 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      colCert_147_122_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_122_22 (hp : 22 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 22 (transLenTr ⟨122, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 22 (transLenTr ⟨122, by decide⟩ 22 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 22 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 22 (transLenTr ⟨122, by decide⟩ 22 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_22.D1 (m := 1) from colCertDiv_147_122_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 22 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_22.D2 (m := 1) from colCertDiv_147_122_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_22_match


theorem leaf_147_122_23 (hp : 23 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 23 (transLenTr ⟨122, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 23 (transLenTr ⟨122, by decide⟩ 23 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 23 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 23 (transLenTr ⟨122, by decide⟩ 23 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_23.D1 (m := 1) from colCertDiv_147_122_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 23 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_23.D2 (m := 1) from colCertDiv_147_122_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_23_match


theorem leaf_147_122_24 (hp : 24 < (Q2.transData.getD 122 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ 24 (transLenTr ⟨122, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨122, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨122, by decide⟩ 24 (transLenTr ⟨122, by decide⟩ 24 hp)) T147_122
      hfix147_122 hinj147_122 hcardT147_122
      (fun i => conj_mem_of_fixedPoints _ _ (T147_122 i) (hfix147_122 i) _)
      ⟨147, by decide⟩ ⟨122, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨122, by decide⟩ 24 hp) Q2.T147_122_2 Q2.hfix147_122_2 Q2.hinj147_122_2
      Q2.hcardT147_122_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_122_2 i) (Q2.hfix147_122_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨122, by decide⟩ 24 (transLenTr ⟨122, by decide⟩ 24 hp) : ↥(reps ⟨122, by decide⟩)) : Coordinate 1)
        T147_122 = colFn colCertDiv_147_122_24.D1 (m := 1) from colCertDiv_147_122_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨122, by decide⟩ 24 hp : ↥(Q2.reps ⟨122, by decide⟩)) : Coordinate 2)
        Q2.T147_122_2 = colFn colCertDiv_147_122_24.D2 (m := 1) from colCertDiv_147_122_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_122_24_match


theorem leaf_147_123_0 (hp : 0 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 0 (transLenTr ⟨123, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 0 (transLenTr ⟨123, by decide⟩ 0 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 0 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      colCert_147_123_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_123_1 (hp : 1 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 1 (transLenTr ⟨123, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 1 (transLenTr ⟨123, by decide⟩ 1 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 1 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 1 (transLenTr ⟨123, by decide⟩ 1 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_1.D1 (m := 1) from colCertDiv_147_123_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 1 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_1.D2 (m := 1) from colCertDiv_147_123_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_1_match


theorem leaf_147_123_2 (hp : 2 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 2 (transLenTr ⟨123, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 2 (transLenTr ⟨123, by decide⟩ 2 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 2 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 2 (transLenTr ⟨123, by decide⟩ 2 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_2.D1 (m := 1) from colCertDiv_147_123_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 2 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_2.D2 (m := 1) from colCertDiv_147_123_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_2_match


theorem leaf_147_123_3 (hp : 3 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 3 (transLenTr ⟨123, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 3 (transLenTr ⟨123, by decide⟩ 3 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 3 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 3 (transLenTr ⟨123, by decide⟩ 3 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_3.D1 (m := 1) from colCertDiv_147_123_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 3 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_3.D2 (m := 1) from colCertDiv_147_123_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_3_match


theorem leaf_147_123_4 (hp : 4 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 4 (transLenTr ⟨123, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 4 (transLenTr ⟨123, by decide⟩ 4 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 4 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 4 (transLenTr ⟨123, by decide⟩ 4 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_4.D1 (m := 1) from colCertDiv_147_123_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 4 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_4.D2 (m := 1) from colCertDiv_147_123_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_4_match


theorem leaf_147_123_5 (hp : 5 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 5 (transLenTr ⟨123, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 5 (transLenTr ⟨123, by decide⟩ 5 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 5 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 5 (transLenTr ⟨123, by decide⟩ 5 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_5.D1 (m := 1) from colCertDiv_147_123_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 5 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_5.D2 (m := 1) from colCertDiv_147_123_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_5_match


theorem leaf_147_123_6 (hp : 6 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 6 (transLenTr ⟨123, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 6 (transLenTr ⟨123, by decide⟩ 6 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 6 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 6 (transLenTr ⟨123, by decide⟩ 6 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_6.D1 (m := 1) from colCertDiv_147_123_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 6 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_6.D2 (m := 1) from colCertDiv_147_123_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_6_match


theorem leaf_147_123_7 (hp : 7 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 7 (transLenTr ⟨123, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 7 (transLenTr ⟨123, by decide⟩ 7 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 7 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      colCert_147_123_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_123_8 (hp : 8 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 8 (transLenTr ⟨123, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 8 (transLenTr ⟨123, by decide⟩ 8 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 8 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 8 (transLenTr ⟨123, by decide⟩ 8 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_8.D1 (m := 1) from colCertDiv_147_123_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 8 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_8.D2 (m := 1) from colCertDiv_147_123_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_8_match


theorem leaf_147_123_9 (hp : 9 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 9 (transLenTr ⟨123, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 9 (transLenTr ⟨123, by decide⟩ 9 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 9 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 9 (transLenTr ⟨123, by decide⟩ 9 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_9.D1 (m := 1) from colCertDiv_147_123_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 9 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_9.D2 (m := 1) from colCertDiv_147_123_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_9_match


theorem leaf_147_123_10 (hp : 10 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 10 (transLenTr ⟨123, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 10 (transLenTr ⟨123, by decide⟩ 10 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 10 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 10 (transLenTr ⟨123, by decide⟩ 10 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_10.D1 (m := 1) from colCertDiv_147_123_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 10 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_10.D2 (m := 1) from colCertDiv_147_123_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_10_match


theorem leaf_147_123_11 (hp : 11 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 11 (transLenTr ⟨123, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 11 (transLenTr ⟨123, by decide⟩ 11 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 11 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 11 (transLenTr ⟨123, by decide⟩ 11 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_11.D1 (m := 1) from colCertDiv_147_123_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 11 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_11.D2 (m := 1) from colCertDiv_147_123_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_11_match


theorem leaf_147_123_12 (hp : 12 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 12 (transLenTr ⟨123, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 12 (transLenTr ⟨123, by decide⟩ 12 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 12 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 12 (transLenTr ⟨123, by decide⟩ 12 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_12.D1 (m := 1) from colCertDiv_147_123_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 12 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_12.D2 (m := 1) from colCertDiv_147_123_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_12_match


theorem leaf_147_123_13 (hp : 13 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 13 (transLenTr ⟨123, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 13 (transLenTr ⟨123, by decide⟩ 13 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 13 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 13 (transLenTr ⟨123, by decide⟩ 13 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_13.D1 (m := 1) from colCertDiv_147_123_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 13 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_13.D2 (m := 1) from colCertDiv_147_123_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_13_match


theorem leaf_147_123_14 (hp : 14 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 14 (transLenTr ⟨123, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 14 (transLenTr ⟨123, by decide⟩ 14 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 14 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      colCert_147_123_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_123_15 (hp : 15 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 15 (transLenTr ⟨123, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 15 (transLenTr ⟨123, by decide⟩ 15 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 15 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 15 (transLenTr ⟨123, by decide⟩ 15 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_15.D1 (m := 1) from colCertDiv_147_123_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 15 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_15.D2 (m := 1) from colCertDiv_147_123_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_15_match


theorem leaf_147_123_16 (hp : 16 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 16 (transLenTr ⟨123, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 16 (transLenTr ⟨123, by decide⟩ 16 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 16 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      colCert_147_123_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_123_17 (hp : 17 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 17 (transLenTr ⟨123, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 17 (transLenTr ⟨123, by decide⟩ 17 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 17 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 17 (transLenTr ⟨123, by decide⟩ 17 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_17.D1 (m := 1) from colCertDiv_147_123_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 17 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_17.D2 (m := 1) from colCertDiv_147_123_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_17_match


theorem leaf_147_123_18 (hp : 18 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 18 (transLenTr ⟨123, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 18 (transLenTr ⟨123, by decide⟩ 18 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 18 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 18 (transLenTr ⟨123, by decide⟩ 18 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_18.D1 (m := 1) from colCertDiv_147_123_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 18 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_18.D2 (m := 1) from colCertDiv_147_123_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_18_match


theorem leaf_147_123_19 (hp : 19 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 19 (transLenTr ⟨123, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 19 (transLenTr ⟨123, by decide⟩ 19 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 19 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 19 (transLenTr ⟨123, by decide⟩ 19 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_19.D1 (m := 1) from colCertDiv_147_123_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 19 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_19.D2 (m := 1) from colCertDiv_147_123_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_19_match


theorem leaf_147_123_20 (hp : 20 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 20 (transLenTr ⟨123, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 20 (transLenTr ⟨123, by decide⟩ 20 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 20 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 20 (transLenTr ⟨123, by decide⟩ 20 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_20.D1 (m := 1) from colCertDiv_147_123_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 20 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_20.D2 (m := 1) from colCertDiv_147_123_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_20_match


theorem leaf_147_123_21 (hp : 21 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 21 (transLenTr ⟨123, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 21 (transLenTr ⟨123, by decide⟩ 21 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 21 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 21 (transLenTr ⟨123, by decide⟩ 21 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_21.D1 (m := 1) from colCertDiv_147_123_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 21 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_21.D2 (m := 1) from colCertDiv_147_123_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_21_match


theorem leaf_147_123_22 (hp : 22 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 22 (transLenTr ⟨123, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 22 (transLenTr ⟨123, by decide⟩ 22 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 22 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 22 (transLenTr ⟨123, by decide⟩ 22 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_22.D1 (m := 1) from colCertDiv_147_123_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 22 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_22.D2 (m := 1) from colCertDiv_147_123_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_22_match


theorem leaf_147_123_23 (hp : 23 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 23 (transLenTr ⟨123, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 23 (transLenTr ⟨123, by decide⟩ 23 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 23 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      colCert_147_123_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_123_24 (hp : 24 < (Q2.transData.getD 123 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ 24 (transLenTr ⟨123, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨123, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨123, by decide⟩ 24 (transLenTr ⟨123, by decide⟩ 24 hp)) T147_123
      hfix147_123 hinj147_123 hcardT147_123
      (fun i => conj_mem_of_fixedPoints _ _ (T147_123 i) (hfix147_123 i) _)
      ⟨147, by decide⟩ ⟨123, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨123, by decide⟩ 24 hp) Q2.T147_123_2 Q2.hfix147_123_2 Q2.hinj147_123_2
      Q2.hcardT147_123_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_123_2 i) (Q2.hfix147_123_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨123, by decide⟩ 24 (transLenTr ⟨123, by decide⟩ 24 hp) : ↥(reps ⟨123, by decide⟩)) : Coordinate 1)
        T147_123 = colFn colCertDiv_147_123_24.D1 (m := 1) from colCertDiv_147_123_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨123, by decide⟩ 24 hp : ↥(Q2.reps ⟨123, by decide⟩)) : Coordinate 2)
        Q2.T147_123_2 = colFn colCertDiv_147_123_24.D2 (m := 1) from colCertDiv_147_123_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_123_24_match


theorem leaf_147_124_0 (hp : 0 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 0 (transLenTr ⟨124, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 0 (transLenTr ⟨124, by decide⟩ 0 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 0 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      colCert_147_124_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_124_1 (hp : 1 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 1 (transLenTr ⟨124, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 1 (transLenTr ⟨124, by decide⟩ 1 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 1 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 1 (transLenTr ⟨124, by decide⟩ 1 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_1.D1 (m := 1) from colCertDiv_147_124_1.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 1 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_1.D2 (m := 1) from colCertDiv_147_124_1.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_1_match


theorem leaf_147_124_2 (hp : 2 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 2 (transLenTr ⟨124, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 2 (transLenTr ⟨124, by decide⟩ 2 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 2 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 2 (transLenTr ⟨124, by decide⟩ 2 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_2.D1 (m := 1) from colCertDiv_147_124_2.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 2 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_2.D2 (m := 1) from colCertDiv_147_124_2.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_2_match


theorem leaf_147_124_3 (hp : 3 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 3 (transLenTr ⟨124, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 3 (transLenTr ⟨124, by decide⟩ 3 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 3 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 3 (transLenTr ⟨124, by decide⟩ 3 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_3.D1 (m := 1) from colCertDiv_147_124_3.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 3 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_3.D2 (m := 1) from colCertDiv_147_124_3.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_3_match


theorem leaf_147_124_4 (hp : 4 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 4 (transLenTr ⟨124, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 4 (transLenTr ⟨124, by decide⟩ 4 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 4 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 4 (transLenTr ⟨124, by decide⟩ 4 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_4.D1 (m := 1) from colCertDiv_147_124_4.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 4 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_4.D2 (m := 1) from colCertDiv_147_124_4.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_4_match


theorem leaf_147_124_5 (hp : 5 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 5 (transLenTr ⟨124, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 5 (transLenTr ⟨124, by decide⟩ 5 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 5 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 5 (transLenTr ⟨124, by decide⟩ 5 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_5.D1 (m := 1) from colCertDiv_147_124_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 5 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_5.D2 (m := 1) from colCertDiv_147_124_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_5_match


theorem leaf_147_124_6 (hp : 6 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 6 (transLenTr ⟨124, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 6 (transLenTr ⟨124, by decide⟩ 6 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 6 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 6 (transLenTr ⟨124, by decide⟩ 6 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_6.D1 (m := 1) from colCertDiv_147_124_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 6 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_6.D2 (m := 1) from colCertDiv_147_124_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_6_match


theorem leaf_147_124_7 (hp : 7 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 7 (transLenTr ⟨124, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 7 (transLenTr ⟨124, by decide⟩ 7 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 7 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 7 (transLenTr ⟨124, by decide⟩ 7 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_7.D1 (m := 1) from colCertDiv_147_124_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 7 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_7.D2 (m := 1) from colCertDiv_147_124_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_7_match


theorem leaf_147_124_8 (hp : 8 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 8 (transLenTr ⟨124, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 8 (transLenTr ⟨124, by decide⟩ 8 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 8 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      colCert_147_124_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_124_9 (hp : 9 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 9 (transLenTr ⟨124, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 9 (transLenTr ⟨124, by decide⟩ 9 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 9 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 9 (transLenTr ⟨124, by decide⟩ 9 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_9.D1 (m := 1) from colCertDiv_147_124_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 9 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_9.D2 (m := 1) from colCertDiv_147_124_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_9_match


theorem leaf_147_124_10 (hp : 10 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 10 (transLenTr ⟨124, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 10 (transLenTr ⟨124, by decide⟩ 10 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 10 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 10 (transLenTr ⟨124, by decide⟩ 10 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_10.D1 (m := 1) from colCertDiv_147_124_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 10 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_10.D2 (m := 1) from colCertDiv_147_124_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_10_match


theorem leaf_147_124_11 (hp : 11 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 11 (transLenTr ⟨124, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 11 (transLenTr ⟨124, by decide⟩ 11 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 11 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      colCert_147_124_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_124_12 (hp : 12 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 12 (transLenTr ⟨124, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 12 (transLenTr ⟨124, by decide⟩ 12 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 12 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 12 (transLenTr ⟨124, by decide⟩ 12 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_12.D1 (m := 1) from colCertDiv_147_124_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 12 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_12.D2 (m := 1) from colCertDiv_147_124_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_12_match


theorem leaf_147_124_13 (hp : 13 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 13 (transLenTr ⟨124, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 13 (transLenTr ⟨124, by decide⟩ 13 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 13 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 13 (transLenTr ⟨124, by decide⟩ 13 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_13.D1 (m := 1) from colCertDiv_147_124_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 13 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_13.D2 (m := 1) from colCertDiv_147_124_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_13_match


theorem leaf_147_124_14 (hp : 14 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 14 (transLenTr ⟨124, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 14 (transLenTr ⟨124, by decide⟩ 14 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 14 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 14 (transLenTr ⟨124, by decide⟩ 14 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_14.D1 (m := 1) from colCertDiv_147_124_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 14 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_14.D2 (m := 1) from colCertDiv_147_124_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_14_match


theorem leaf_147_124_15 (hp : 15 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 15 (transLenTr ⟨124, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 15 (transLenTr ⟨124, by decide⟩ 15 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 15 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 15 (transLenTr ⟨124, by decide⟩ 15 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_15.D1 (m := 1) from colCertDiv_147_124_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 15 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_15.D2 (m := 1) from colCertDiv_147_124_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_15_match


theorem leaf_147_124_16 (hp : 16 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 16 (transLenTr ⟨124, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 16 (transLenTr ⟨124, by decide⟩ 16 hp)) T147_124
      hfix147_124 hinj147_124 hcardT147_124
      (fun i => conj_mem_of_fixedPoints _ _ (T147_124 i) (hfix147_124 i) _)
      ⟨147, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 16 hp) Q2.T147_124_2 Q2.hfix147_124_2 Q2.hinj147_124_2
      Q2.hcardT147_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_124_2 i) (Q2.hfix147_124_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨124, by decide⟩ 16 (transLenTr ⟨124, by decide⟩ 16 hp) : ↥(reps ⟨124, by decide⟩)) : Coordinate 1)
        T147_124 = colFn colCertDiv_147_124_16.D1 (m := 1) from colCertDiv_147_124_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨124, by decide⟩ 16 hp : ↥(Q2.reps ⟨124, by decide⟩)) : Coordinate 2)
        Q2.T147_124_2 = colFn colCertDiv_147_124_16.D2 (m := 1) from colCertDiv_147_124_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_124_16_match


end LeanDring.P5Presentation
