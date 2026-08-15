/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C011
import LeanDring.P5.Data.ColCdd.C010
import LeanDring.P5.Data.ColRestCheap.C054
import LeanDring.P5.Data.ColRestCheap.C055
import LeanDring.P5.Data.ColRestCheap.C056
import LeanDring.P5.Data.ColRestCheap.C057
import LeanDring.P5.Data.EntryK.C031
import LeanDring.P5.Data.EntryK.C032
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C068
import LeanDring.P5.Data.SpeciesDiv.C069
import LeanDring.P5.Data.SpeciesDiv.C009
import LeanDring.P5.Data.SpeciesDiv.C010

/-! # Stage-5 leaves, chunk 32 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_124_113_20 (hp : 20 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨124, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp)) T124_113
      hfix124_113 hinj124_113 hcardT124_113
      (fun i => conj_mem_of_fixedPoints _ _ (T124_113 i) (hfix124_113 i) _)
      ⟨124, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 20 hp) Q2.T124_113_2 Q2.hfix124_113_2 Q2.hinj124_113_2
      Q2.hcardT124_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_113_2 i) (Q2.hfix124_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨124, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T124_113 = colFn colCertDiv_124_113_20.D1 (m := 5) from colCertDiv_124_113_20.bind1,
    show colData2 (⟨124, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 20 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T124_113_2 = colFn colCertDiv_124_113_20.D2 (m := 5) from colCertDiv_124_113_20.bind2]
  rw [alnId_124 j hj]
  exact fastcode_of_div ⟨124, by decide⟩ _ _ _
    ((alnId_124 j hj) ▸ Q2.listedAt (⟨124, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨124, by decide⟩ : Fin 148) hj hq).1) colCertDiv_124_113_20_match


theorem leaf_124_124_0 (hp : 0 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 0 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 0 (transLenTr ⟨124, by decide⟩ 0 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 0 (transLenTr ⟨124, by decide⟩ 0 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 0 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_0.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_1 (hp : 1 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 1 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 1 (transLenTr ⟨124, by decide⟩ 1 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 1 (transLenTr ⟨124, by decide⟩ 1 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 1 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_1.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_2 (hp : 2 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 2 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 2 (transLenTr ⟨124, by decide⟩ 2 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 2 (transLenTr ⟨124, by decide⟩ 2 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 2 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_2.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_3 (hp : 3 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 3 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 3 (transLenTr ⟨124, by decide⟩ 3 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 3 (transLenTr ⟨124, by decide⟩ 3 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 3 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_3.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_4 (hp : 4 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 4 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 4 (transLenTr ⟨124, by decide⟩ 4 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 4 (transLenTr ⟨124, by decide⟩ 4 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 4 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_4.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_5 (hp : 5 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 5 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 5 (transLenTr ⟨124, by decide⟩ 5 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 5 (transLenTr ⟨124, by decide⟩ 5 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 5 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_5.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_6 (hp : 6 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 6 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 6 (transLenTr ⟨124, by decide⟩ 6 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 6 (transLenTr ⟨124, by decide⟩ 6 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 6 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_6.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_7 (hp : 7 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 7 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 7 (transLenTr ⟨124, by decide⟩ 7 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 7 (transLenTr ⟨124, by decide⟩ 7 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 7 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_7.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_8 (hp : 8 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 8 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 8 (transLenTr ⟨124, by decide⟩ 8 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 8 (transLenTr ⟨124, by decide⟩ 8 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 8 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_8.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_9 (hp : 9 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 9 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 9 (transLenTr ⟨124, by decide⟩ 9 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 9 (transLenTr ⟨124, by decide⟩ 9 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 9 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_9.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_10 (hp : 10 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 10 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 10 (transLenTr ⟨124, by decide⟩ 10 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 10 (transLenTr ⟨124, by decide⟩ 10 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 10 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_10.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_11 (hp : 11 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 11 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 11 (transLenTr ⟨124, by decide⟩ 11 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 11 (transLenTr ⟨124, by decide⟩ 11 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 11 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_11.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_12 (hp : 12 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 12 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 12 (transLenTr ⟨124, by decide⟩ 12 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 12 (transLenTr ⟨124, by decide⟩ 12 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 12 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_12.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_13 (hp : 13 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 13 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 13 (transLenTr ⟨124, by decide⟩ 13 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 13 (transLenTr ⟨124, by decide⟩ 13 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 13 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_13.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_14 (hp : 14 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 14 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 14 (transLenTr ⟨124, by decide⟩ 14 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 14 (transLenTr ⟨124, by decide⟩ 14 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 14 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_14.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_15 (hp : 15 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 15 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 15 (transLenTr ⟨124, by decide⟩ 15 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 15 (transLenTr ⟨124, by decide⟩ 15 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 15 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_15.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_16 (hp : 16 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 16 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 16 (transLenTr ⟨124, by decide⟩ 16 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 16 (transLenTr ⟨124, by decide⟩ 16 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 16 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_16.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_17 (hp : 17 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 17 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 17 (transLenTr ⟨124, by decide⟩ 17 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 17 (transLenTr ⟨124, by decide⟩ 17 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 17 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_17.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_18 (hp : 18 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 18 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 18 (transLenTr ⟨124, by decide⟩ 18 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 18 (transLenTr ⟨124, by decide⟩ 18 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 18 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_18.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_19 (hp : 19 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 19 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 19 (transLenTr ⟨124, by decide⟩ 19 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 19 (transLenTr ⟨124, by decide⟩ 19 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 19 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_19.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_20 (hp : 20 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 20 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 20 (transLenTr ⟨124, by decide⟩ 20 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 20 (transLenTr ⟨124, by decide⟩ 20 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 20 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_20.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_21 (hp : 21 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 21 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 21 (transLenTr ⟨124, by decide⟩ 21 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 21 (transLenTr ⟨124, by decide⟩ 21 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 21 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_21.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_22 (hp : 22 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 22 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 22 (transLenTr ⟨124, by decide⟩ 22 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 22 (transLenTr ⟨124, by decide⟩ 22 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 22 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_22.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_23 (hp : 23 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 23 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 23 (transLenTr ⟨124, by decide⟩ 23 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 23 (transLenTr ⟨124, by decide⟩ 23 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 23 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_23.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_124_124_24 (hp : 24 < (Q2.transData.getD 124 []).length)
    (j : Nat) (hj : j < (repChars.getD 124 []).length)
    (hq : (normIsRep.getD 124 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ 24 hp)
        (rowE2 (⟨124, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ 24 (transLenTr ⟨124, by decide⟩ 24 hp))
        (rowE1 (⟨124, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨124, by decide⟩ : Fin 148) ⟨124, by decide⟩ _
      (validAt ⟨124, by decide⟩ (listedAt ⟨124, by decide⟩ hj))
      (colE1 ⟨124, by decide⟩ 24 (transLenTr ⟨124, by decide⟩ 24 hp)) T124_124
      hfix124_124 hinj124_124 hcardT124_124
      (fun i => conj_mem_of_fixedPoints _ _ (T124_124 i) (hfix124_124 i) _)
      ⟨124, by decide⟩ ⟨124, by decide⟩ _
      (Q2.validAt ⟨124, by decide⟩ (Q2.listedAt ⟨124, by decide⟩
        (alnCheck_rep ⟨124, by decide⟩ hj hq).1))
      (colE2 ⟨124, by decide⟩ 24 hp) Q2.T124_124_2 Q2.hfix124_124_2 Q2.hinj124_124_2
      Q2.hcardT124_124_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T124_124_2 i) (Q2.hfix124_124_2 i) _)
      colCert_124_124_24.hD ?_).symm
  rw [alnId_124 j hj]


theorem leaf_125_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T125_2
      hfix125_2 hinj125_2 hcardT125_2
      (fun i => conj_mem_of_fixedPoints _ _ (T125_2 i) (hfix125_2 i) _)
      ⟨125, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T125_2_2 Q2.hfix125_2_2 Q2.hinj125_2_2
      Q2.hcardT125_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_2_2 i) (Q2.hfix125_2_2 i) _)
      colCert_125_2_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T125_2
      hfix125_2 hinj125_2 hcardT125_2
      (fun i => conj_mem_of_fixedPoints _ _ (T125_2 i) (hfix125_2 i) _)
      ⟨125, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T125_2_2 Q2.hfix125_2_2 Q2.hinj125_2_2
      Q2.hcardT125_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_2_2 i) (Q2.hfix125_2_2 i) _)
      colCert_125_2_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T125_2
      hfix125_2 hinj125_2 hcardT125_2
      (fun i => conj_mem_of_fixedPoints _ _ (T125_2 i) (hfix125_2 i) _)
      ⟨125, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T125_2_2 Q2.hfix125_2_2 Q2.hinj125_2_2
      Q2.hcardT125_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_2_2 i) (Q2.hfix125_2_2 i) _)
      colCert_125_2_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T125_2
      hfix125_2 hinj125_2 hcardT125_2
      (fun i => conj_mem_of_fixedPoints _ _ (T125_2 i) (hfix125_2 i) _)
      ⟨125, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T125_2_2 Q2.hfix125_2_2 Q2.hinj125_2_2
      Q2.hcardT125_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_2_2 i) (Q2.hfix125_2_2 i) _)
      colCert_125_2_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T125_2
      hfix125_2 hinj125_2 hcardT125_2
      (fun i => conj_mem_of_fixedPoints _ _ (T125_2 i) (hfix125_2 i) _)
      ⟨125, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T125_2_2 Q2.hfix125_2_2 Q2.hinj125_2_2
      Q2.hcardT125_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_2_2 i) (Q2.hfix125_2_2 i) _)
      colCert_125_2_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T125_10
      hfix125_10 hinj125_10 hcardT125_10
      (fun i => conj_mem_of_fixedPoints _ _ (T125_10 i) (hfix125_10 i) _)
      ⟨125, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T125_10_2 Q2.hfix125_10_2 Q2.hinj125_10_2
      Q2.hcardT125_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_10_2 i) (Q2.hfix125_10_2 i) _)
      colCert_125_10_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T125_10
      hfix125_10 hinj125_10 hcardT125_10
      (fun i => conj_mem_of_fixedPoints _ _ (T125_10 i) (hfix125_10 i) _)
      ⟨125, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T125_10_2 Q2.hfix125_10_2 Q2.hinj125_10_2
      Q2.hcardT125_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_10_2 i) (Q2.hfix125_10_2 i) _)
      colCert_125_10_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T125_10
      hfix125_10 hinj125_10 hcardT125_10
      (fun i => conj_mem_of_fixedPoints _ _ (T125_10 i) (hfix125_10 i) _)
      ⟨125, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T125_10_2 Q2.hfix125_10_2 Q2.hinj125_10_2
      Q2.hcardT125_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_10_2 i) (Q2.hfix125_10_2 i) _)
      colCert_125_10_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T125_10
      hfix125_10 hinj125_10 hcardT125_10
      (fun i => conj_mem_of_fixedPoints _ _ (T125_10 i) (hfix125_10 i) _)
      ⟨125, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T125_10_2 Q2.hfix125_10_2 Q2.hinj125_10_2
      Q2.hcardT125_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_10_2 i) (Q2.hfix125_10_2 i) _)
      colCert_125_10_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T125_10
      hfix125_10 hinj125_10 hcardT125_10
      (fun i => conj_mem_of_fixedPoints _ _ (T125_10 i) (hfix125_10 i) _)
      ⟨125, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T125_10_2 Q2.hfix125_10_2 Q2.hinj125_10_2
      Q2.hcardT125_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_10_2 i) (Q2.hfix125_10_2 i) _)
      colCert_125_10_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T125_12
      hfix125_12 hinj125_12 hcardT125_12
      (fun i => conj_mem_of_fixedPoints _ _ (T125_12 i) (hfix125_12 i) _)
      ⟨125, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T125_12_2 Q2.hfix125_12_2 Q2.hinj125_12_2
      Q2.hcardT125_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_12_2 i) (Q2.hfix125_12_2 i) _)
      colCert_125_12_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T125_12
      hfix125_12 hinj125_12 hcardT125_12
      (fun i => conj_mem_of_fixedPoints _ _ (T125_12 i) (hfix125_12 i) _)
      ⟨125, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T125_12_2 Q2.hfix125_12_2 Q2.hinj125_12_2
      Q2.hcardT125_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_12_2 i) (Q2.hfix125_12_2 i) _)
      colCert_125_12_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T125_12
      hfix125_12 hinj125_12 hcardT125_12
      (fun i => conj_mem_of_fixedPoints _ _ (T125_12 i) (hfix125_12 i) _)
      ⟨125, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T125_12_2 Q2.hfix125_12_2 Q2.hinj125_12_2
      Q2.hcardT125_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_12_2 i) (Q2.hfix125_12_2 i) _)
      colCert_125_12_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T125_12
      hfix125_12 hinj125_12 hcardT125_12
      (fun i => conj_mem_of_fixedPoints _ _ (T125_12 i) (hfix125_12 i) _)
      ⟨125, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T125_12_2 Q2.hfix125_12_2 Q2.hinj125_12_2
      Q2.hcardT125_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_12_2 i) (Q2.hfix125_12_2 i) _)
      colCert_125_12_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T125_12
      hfix125_12 hinj125_12 hcardT125_12
      (fun i => conj_mem_of_fixedPoints _ _ (T125_12 i) (hfix125_12 i) _)
      ⟨125, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T125_12_2 Q2.hfix125_12_2 Q2.hinj125_12_2
      Q2.hcardT125_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_12_2 i) (Q2.hfix125_12_2 i) _)
      colCert_125_12_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T125_20
      hfix125_20 hinj125_20 hcardT125_20
      (fun i => conj_mem_of_fixedPoints _ _ (T125_20 i) (hfix125_20 i) _)
      ⟨125, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T125_20_2 Q2.hfix125_20_2 Q2.hinj125_20_2
      Q2.hcardT125_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_20_2 i) (Q2.hfix125_20_2 i) _)
      colCert_125_20_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T125_20
      hfix125_20 hinj125_20 hcardT125_20
      (fun i => conj_mem_of_fixedPoints _ _ (T125_20 i) (hfix125_20 i) _)
      ⟨125, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T125_20_2 Q2.hfix125_20_2 Q2.hinj125_20_2
      Q2.hcardT125_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_20_2 i) (Q2.hfix125_20_2 i) _)
      colCert_125_20_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T125_20
      hfix125_20 hinj125_20 hcardT125_20
      (fun i => conj_mem_of_fixedPoints _ _ (T125_20 i) (hfix125_20 i) _)
      ⟨125, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T125_20_2 Q2.hfix125_20_2 Q2.hinj125_20_2
      Q2.hcardT125_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_20_2 i) (Q2.hfix125_20_2 i) _)
      colCert_125_20_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T125_20
      hfix125_20 hinj125_20 hcardT125_20
      (fun i => conj_mem_of_fixedPoints _ _ (T125_20 i) (hfix125_20 i) _)
      ⟨125, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T125_20_2 Q2.hfix125_20_2 Q2.hinj125_20_2
      Q2.hcardT125_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_20_2 i) (Q2.hfix125_20_2 i) _)
      colCert_125_20_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T125_20
      hfix125_20 hinj125_20 hcardT125_20
      (fun i => conj_mem_of_fixedPoints _ _ (T125_20 i) (hfix125_20 i) _)
      ⟨125, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T125_20_2 Q2.hfix125_20_2 Q2.hinj125_20_2
      Q2.hcardT125_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_20_2 i) (Q2.hfix125_20_2 i) _)
      colCert_125_20_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T125_20
      hfix125_20 hinj125_20 hcardT125_20
      (fun i => conj_mem_of_fixedPoints _ _ (T125_20 i) (hfix125_20 i) _)
      ⟨125, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T125_20_2 Q2.hfix125_20_2 Q2.hinj125_20_2
      Q2.hcardT125_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_20_2 i) (Q2.hfix125_20_2 i) _)
      colCert_125_20_5.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T125_20
      hfix125_20 hinj125_20 hcardT125_20
      (fun i => conj_mem_of_fixedPoints _ _ (T125_20 i) (hfix125_20 i) _)
      ⟨125, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T125_20_2 Q2.hfix125_20_2 Q2.hinj125_20_2
      Q2.hcardT125_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_20_2 i) (Q2.hfix125_20_2 i) _)
      colCert_125_20_10.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T125_20
      hfix125_20 hinj125_20 hcardT125_20
      (fun i => conj_mem_of_fixedPoints _ _ (T125_20 i) (hfix125_20 i) _)
      ⟨125, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T125_20_2 Q2.hfix125_20_2 Q2.hinj125_20_2
      Q2.hcardT125_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_20_2 i) (Q2.hfix125_20_2 i) _)
      colCert_125_20_15.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T125_20
      hfix125_20 hinj125_20 hcardT125_20
      (fun i => conj_mem_of_fixedPoints _ _ (T125_20 i) (hfix125_20 i) _)
      ⟨125, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T125_20_2 Q2.hfix125_20_2 Q2.hinj125_20_2
      Q2.hcardT125_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_20_2 i) (Q2.hfix125_20_2 i) _)
      colCert_125_20_20.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T125_31
      hfix125_31 hinj125_31 hcardT125_31
      (fun i => conj_mem_of_fixedPoints _ _ (T125_31 i) (hfix125_31 i) _)
      ⟨125, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T125_31_2 Q2.hfix125_31_2 Q2.hinj125_31_2
      Q2.hcardT125_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_31_2 i) (Q2.hfix125_31_2 i) _)
      colCert_125_31_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T125_31
      hfix125_31 hinj125_31 hcardT125_31
      (fun i => conj_mem_of_fixedPoints _ _ (T125_31 i) (hfix125_31 i) _)
      ⟨125, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T125_31_2 Q2.hfix125_31_2 Q2.hinj125_31_2
      Q2.hcardT125_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_31_2 i) (Q2.hfix125_31_2 i) _)
      colCert_125_31_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T125_31
      hfix125_31 hinj125_31 hcardT125_31
      (fun i => conj_mem_of_fixedPoints _ _ (T125_31 i) (hfix125_31 i) _)
      ⟨125, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T125_31_2 Q2.hfix125_31_2 Q2.hinj125_31_2
      Q2.hcardT125_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_31_2 i) (Q2.hfix125_31_2 i) _)
      colCert_125_31_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T125_31
      hfix125_31 hinj125_31 hcardT125_31
      (fun i => conj_mem_of_fixedPoints _ _ (T125_31 i) (hfix125_31 i) _)
      ⟨125, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T125_31_2 Q2.hfix125_31_2 Q2.hinj125_31_2
      Q2.hcardT125_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_31_2 i) (Q2.hfix125_31_2 i) _)
      colCert_125_31_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T125_31
      hfix125_31 hinj125_31 hcardT125_31
      (fun i => conj_mem_of_fixedPoints _ _ (T125_31 i) (hfix125_31 i) _)
      ⟨125, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T125_31_2 Q2.hfix125_31_2 Q2.hinj125_31_2
      Q2.hcardT125_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_31_2 i) (Q2.hfix125_31_2 i) _)
      colCert_125_31_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T125_31
      hfix125_31 hinj125_31 hcardT125_31
      (fun i => conj_mem_of_fixedPoints _ _ (T125_31 i) (hfix125_31 i) _)
      ⟨125, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T125_31_2 Q2.hfix125_31_2 Q2.hinj125_31_2
      Q2.hcardT125_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_31_2 i) (Q2.hfix125_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T125_31 = colFn colCertDiv_125_31_5.D1 (m := 5) from colCertDiv_125_31_5.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 5 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T125_31_2 = colFn colCertDiv_125_31_5.D2 (m := 5) from colCertDiv_125_31_5.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_31_5_match


theorem leaf_125_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T125_31
      hfix125_31 hinj125_31 hcardT125_31
      (fun i => conj_mem_of_fixedPoints _ _ (T125_31 i) (hfix125_31 i) _)
      ⟨125, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T125_31_2 Q2.hfix125_31_2 Q2.hinj125_31_2
      Q2.hcardT125_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_31_2 i) (Q2.hfix125_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T125_31 = colFn colCertDiv_125_31_10.D1 (m := 5) from colCertDiv_125_31_10.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 10 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T125_31_2 = colFn colCertDiv_125_31_10.D2 (m := 5) from colCertDiv_125_31_10.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_31_10_match


theorem leaf_125_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T125_31
      hfix125_31 hinj125_31 hcardT125_31
      (fun i => conj_mem_of_fixedPoints _ _ (T125_31 i) (hfix125_31 i) _)
      ⟨125, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T125_31_2 Q2.hfix125_31_2 Q2.hinj125_31_2
      Q2.hcardT125_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_31_2 i) (Q2.hfix125_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T125_31 = colFn colCertDiv_125_31_15.D1 (m := 5) from colCertDiv_125_31_15.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 15 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T125_31_2 = colFn colCertDiv_125_31_15.D2 (m := 5) from colCertDiv_125_31_15.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_31_15_match


theorem leaf_125_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T125_31
      hfix125_31 hinj125_31 hcardT125_31
      (fun i => conj_mem_of_fixedPoints _ _ (T125_31 i) (hfix125_31 i) _)
      ⟨125, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T125_31_2 Q2.hfix125_31_2 Q2.hinj125_31_2
      Q2.hcardT125_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_31_2 i) (Q2.hfix125_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T125_31 = colFn colCertDiv_125_31_20.D1 (m := 5) from colCertDiv_125_31_20.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 20 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T125_31_2 = colFn colCertDiv_125_31_20.D2 (m := 5) from colCertDiv_125_31_20.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_31_20_match


theorem leaf_125_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T125_34
      hfix125_34 hinj125_34 hcardT125_34
      (fun i => conj_mem_of_fixedPoints _ _ (T125_34 i) (hfix125_34 i) _)
      ⟨125, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T125_34_2 Q2.hfix125_34_2 Q2.hinj125_34_2
      Q2.hcardT125_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_34_2 i) (Q2.hfix125_34_2 i) _)
      colCert_125_34_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T125_34
      hfix125_34 hinj125_34 hcardT125_34
      (fun i => conj_mem_of_fixedPoints _ _ (T125_34 i) (hfix125_34 i) _)
      ⟨125, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T125_34_2 Q2.hfix125_34_2 Q2.hinj125_34_2
      Q2.hcardT125_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_34_2 i) (Q2.hfix125_34_2 i) _)
      colCert_125_34_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T125_34
      hfix125_34 hinj125_34 hcardT125_34
      (fun i => conj_mem_of_fixedPoints _ _ (T125_34 i) (hfix125_34 i) _)
      ⟨125, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T125_34_2 Q2.hfix125_34_2 Q2.hinj125_34_2
      Q2.hcardT125_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_34_2 i) (Q2.hfix125_34_2 i) _)
      colCert_125_34_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T125_34
      hfix125_34 hinj125_34 hcardT125_34
      (fun i => conj_mem_of_fixedPoints _ _ (T125_34 i) (hfix125_34 i) _)
      ⟨125, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T125_34_2 Q2.hfix125_34_2 Q2.hinj125_34_2
      Q2.hcardT125_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_34_2 i) (Q2.hfix125_34_2 i) _)
      colCert_125_34_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T125_34
      hfix125_34 hinj125_34 hcardT125_34
      (fun i => conj_mem_of_fixedPoints _ _ (T125_34 i) (hfix125_34 i) _)
      ⟨125, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T125_34_2 Q2.hfix125_34_2 Q2.hinj125_34_2
      Q2.hcardT125_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_34_2 i) (Q2.hfix125_34_2 i) _)
      colCert_125_34_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T125_34
      hfix125_34 hinj125_34 hcardT125_34
      (fun i => conj_mem_of_fixedPoints _ _ (T125_34 i) (hfix125_34 i) _)
      ⟨125, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T125_34_2 Q2.hfix125_34_2 Q2.hinj125_34_2
      Q2.hcardT125_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_34_2 i) (Q2.hfix125_34_2 i) _)
      colCert_125_34_5.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T125_34
      hfix125_34 hinj125_34 hcardT125_34
      (fun i => conj_mem_of_fixedPoints _ _ (T125_34 i) (hfix125_34 i) _)
      ⟨125, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T125_34_2 Q2.hfix125_34_2 Q2.hinj125_34_2
      Q2.hcardT125_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_34_2 i) (Q2.hfix125_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T125_34 = colFn colCertDiv_125_34_10.D1 (m := 5) from colCertDiv_125_34_10.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 10 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T125_34_2 = colFn colCertDiv_125_34_10.D2 (m := 5) from colCertDiv_125_34_10.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_34_10_match


theorem leaf_125_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T125_34
      hfix125_34 hinj125_34 hcardT125_34
      (fun i => conj_mem_of_fixedPoints _ _ (T125_34 i) (hfix125_34 i) _)
      ⟨125, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T125_34_2 Q2.hfix125_34_2 Q2.hinj125_34_2
      Q2.hcardT125_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_34_2 i) (Q2.hfix125_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T125_34 = colFn colCertDiv_125_34_15.D1 (m := 5) from colCertDiv_125_34_15.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 15 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T125_34_2 = colFn colCertDiv_125_34_15.D2 (m := 5) from colCertDiv_125_34_15.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_34_15_match


theorem leaf_125_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T125_34
      hfix125_34 hinj125_34 hcardT125_34
      (fun i => conj_mem_of_fixedPoints _ _ (T125_34 i) (hfix125_34 i) _)
      ⟨125, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T125_34_2 Q2.hfix125_34_2 Q2.hinj125_34_2
      Q2.hcardT125_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_34_2 i) (Q2.hfix125_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T125_34 = colFn colCertDiv_125_34_20.D1 (m := 5) from colCertDiv_125_34_20.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 20 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T125_34_2 = colFn colCertDiv_125_34_20.D2 (m := 5) from colCertDiv_125_34_20.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_34_20_match


theorem leaf_125_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T125_40
      hfix125_40 hinj125_40 hcardT125_40
      (fun i => conj_mem_of_fixedPoints _ _ (T125_40 i) (hfix125_40 i) _)
      ⟨125, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T125_40_2 Q2.hfix125_40_2 Q2.hinj125_40_2
      Q2.hcardT125_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_40_2 i) (Q2.hfix125_40_2 i) _)
      colCert_125_40_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T125_40
      hfix125_40 hinj125_40 hcardT125_40
      (fun i => conj_mem_of_fixedPoints _ _ (T125_40 i) (hfix125_40 i) _)
      ⟨125, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T125_40_2 Q2.hfix125_40_2 Q2.hinj125_40_2
      Q2.hcardT125_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_40_2 i) (Q2.hfix125_40_2 i) _)
      colCert_125_40_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T125_40
      hfix125_40 hinj125_40 hcardT125_40
      (fun i => conj_mem_of_fixedPoints _ _ (T125_40 i) (hfix125_40 i) _)
      ⟨125, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T125_40_2 Q2.hfix125_40_2 Q2.hinj125_40_2
      Q2.hcardT125_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_40_2 i) (Q2.hfix125_40_2 i) _)
      colCert_125_40_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T125_40
      hfix125_40 hinj125_40 hcardT125_40
      (fun i => conj_mem_of_fixedPoints _ _ (T125_40 i) (hfix125_40 i) _)
      ⟨125, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T125_40_2 Q2.hfix125_40_2 Q2.hinj125_40_2
      Q2.hcardT125_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_40_2 i) (Q2.hfix125_40_2 i) _)
      colCert_125_40_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T125_40
      hfix125_40 hinj125_40 hcardT125_40
      (fun i => conj_mem_of_fixedPoints _ _ (T125_40 i) (hfix125_40 i) _)
      ⟨125, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T125_40_2 Q2.hfix125_40_2 Q2.hinj125_40_2
      Q2.hcardT125_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_40_2 i) (Q2.hfix125_40_2 i) _)
      colCert_125_40_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T125_40
      hfix125_40 hinj125_40 hcardT125_40
      (fun i => conj_mem_of_fixedPoints _ _ (T125_40 i) (hfix125_40 i) _)
      ⟨125, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T125_40_2 Q2.hfix125_40_2 Q2.hinj125_40_2
      Q2.hcardT125_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_40_2 i) (Q2.hfix125_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T125_40 = colFn colCertDiv_125_40_5.D1 (m := 5) from colCertDiv_125_40_5.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 5 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T125_40_2 = colFn colCertDiv_125_40_5.D2 (m := 5) from colCertDiv_125_40_5.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_40_5_match


theorem leaf_125_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T125_40
      hfix125_40 hinj125_40 hcardT125_40
      (fun i => conj_mem_of_fixedPoints _ _ (T125_40 i) (hfix125_40 i) _)
      ⟨125, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T125_40_2 Q2.hfix125_40_2 Q2.hinj125_40_2
      Q2.hcardT125_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_40_2 i) (Q2.hfix125_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T125_40 = colFn colCertDiv_125_40_10.D1 (m := 5) from colCertDiv_125_40_10.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 10 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T125_40_2 = colFn colCertDiv_125_40_10.D2 (m := 5) from colCertDiv_125_40_10.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_40_10_match


theorem leaf_125_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T125_40
      hfix125_40 hinj125_40 hcardT125_40
      (fun i => conj_mem_of_fixedPoints _ _ (T125_40 i) (hfix125_40 i) _)
      ⟨125, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T125_40_2 Q2.hfix125_40_2 Q2.hinj125_40_2
      Q2.hcardT125_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_40_2 i) (Q2.hfix125_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T125_40 = colFn colCertDiv_125_40_15.D1 (m := 5) from colCertDiv_125_40_15.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 15 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T125_40_2 = colFn colCertDiv_125_40_15.D2 (m := 5) from colCertDiv_125_40_15.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_40_15_match


theorem leaf_125_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T125_40
      hfix125_40 hinj125_40 hcardT125_40
      (fun i => conj_mem_of_fixedPoints _ _ (T125_40 i) (hfix125_40 i) _)
      ⟨125, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T125_40_2 Q2.hfix125_40_2 Q2.hinj125_40_2
      Q2.hcardT125_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_40_2 i) (Q2.hfix125_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T125_40 = colFn colCertDiv_125_40_20.D1 (m := 5) from colCertDiv_125_40_20.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 20 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T125_40_2 = colFn colCertDiv_125_40_20.D2 (m := 5) from colCertDiv_125_40_20.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_40_20_match


theorem leaf_125_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T125_43
      hfix125_43 hinj125_43 hcardT125_43
      (fun i => conj_mem_of_fixedPoints _ _ (T125_43 i) (hfix125_43 i) _)
      ⟨125, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T125_43_2 Q2.hfix125_43_2 Q2.hinj125_43_2
      Q2.hcardT125_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_43_2 i) (Q2.hfix125_43_2 i) _)
      colCert_125_43_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T125_43
      hfix125_43 hinj125_43 hcardT125_43
      (fun i => conj_mem_of_fixedPoints _ _ (T125_43 i) (hfix125_43 i) _)
      ⟨125, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T125_43_2 Q2.hfix125_43_2 Q2.hinj125_43_2
      Q2.hcardT125_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_43_2 i) (Q2.hfix125_43_2 i) _)
      colCert_125_43_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T125_43
      hfix125_43 hinj125_43 hcardT125_43
      (fun i => conj_mem_of_fixedPoints _ _ (T125_43 i) (hfix125_43 i) _)
      ⟨125, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T125_43_2 Q2.hfix125_43_2 Q2.hinj125_43_2
      Q2.hcardT125_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_43_2 i) (Q2.hfix125_43_2 i) _)
      colCert_125_43_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T125_43
      hfix125_43 hinj125_43 hcardT125_43
      (fun i => conj_mem_of_fixedPoints _ _ (T125_43 i) (hfix125_43 i) _)
      ⟨125, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T125_43_2 Q2.hfix125_43_2 Q2.hinj125_43_2
      Q2.hcardT125_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_43_2 i) (Q2.hfix125_43_2 i) _)
      colCert_125_43_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T125_43
      hfix125_43 hinj125_43 hcardT125_43
      (fun i => conj_mem_of_fixedPoints _ _ (T125_43 i) (hfix125_43 i) _)
      ⟨125, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T125_43_2 Q2.hfix125_43_2 Q2.hinj125_43_2
      Q2.hcardT125_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_43_2 i) (Q2.hfix125_43_2 i) _)
      colCert_125_43_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T125_43
      hfix125_43 hinj125_43 hcardT125_43
      (fun i => conj_mem_of_fixedPoints _ _ (T125_43 i) (hfix125_43 i) _)
      ⟨125, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T125_43_2 Q2.hfix125_43_2 Q2.hinj125_43_2
      Q2.hcardT125_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_43_2 i) (Q2.hfix125_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T125_43 = colFn colCertDiv_125_43_5.D1 (m := 5) from colCertDiv_125_43_5.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T125_43_2 = colFn colCertDiv_125_43_5.D2 (m := 5) from colCertDiv_125_43_5.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_43_5_match


theorem leaf_125_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T125_43
      hfix125_43 hinj125_43 hcardT125_43
      (fun i => conj_mem_of_fixedPoints _ _ (T125_43 i) (hfix125_43 i) _)
      ⟨125, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T125_43_2 Q2.hfix125_43_2 Q2.hinj125_43_2
      Q2.hcardT125_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_43_2 i) (Q2.hfix125_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T125_43 = colFn colCertDiv_125_43_10.D1 (m := 5) from colCertDiv_125_43_10.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T125_43_2 = colFn colCertDiv_125_43_10.D2 (m := 5) from colCertDiv_125_43_10.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_43_10_match


theorem leaf_125_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T125_43
      hfix125_43 hinj125_43 hcardT125_43
      (fun i => conj_mem_of_fixedPoints _ _ (T125_43 i) (hfix125_43 i) _)
      ⟨125, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T125_43_2 Q2.hfix125_43_2 Q2.hinj125_43_2
      Q2.hcardT125_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_43_2 i) (Q2.hfix125_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T125_43 = colFn colCertDiv_125_43_15.D1 (m := 5) from colCertDiv_125_43_15.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T125_43_2 = colFn colCertDiv_125_43_15.D2 (m := 5) from colCertDiv_125_43_15.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_43_15_match


theorem leaf_125_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T125_43
      hfix125_43 hinj125_43 hcardT125_43
      (fun i => conj_mem_of_fixedPoints _ _ (T125_43 i) (hfix125_43 i) _)
      ⟨125, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T125_43_2 Q2.hfix125_43_2 Q2.hinj125_43_2
      Q2.hcardT125_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_43_2 i) (Q2.hfix125_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T125_43 = colFn colCertDiv_125_43_20.D1 (m := 5) from colCertDiv_125_43_20.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T125_43_2 = colFn colCertDiv_125_43_20.D2 (m := 5) from colCertDiv_125_43_20.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_43_20_match


theorem leaf_125_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T125_52
      hfix125_52 hinj125_52 hcardT125_52
      (fun i => conj_mem_of_fixedPoints _ _ (T125_52 i) (hfix125_52 i) _)
      ⟨125, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T125_52_2 Q2.hfix125_52_2 Q2.hinj125_52_2
      Q2.hcardT125_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_52_2 i) (Q2.hfix125_52_2 i) _)
      colCert_125_52_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T125_52
      hfix125_52 hinj125_52 hcardT125_52
      (fun i => conj_mem_of_fixedPoints _ _ (T125_52 i) (hfix125_52 i) _)
      ⟨125, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T125_52_2 Q2.hfix125_52_2 Q2.hinj125_52_2
      Q2.hcardT125_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_52_2 i) (Q2.hfix125_52_2 i) _)
      colCert_125_52_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T125_52
      hfix125_52 hinj125_52 hcardT125_52
      (fun i => conj_mem_of_fixedPoints _ _ (T125_52 i) (hfix125_52 i) _)
      ⟨125, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T125_52_2 Q2.hfix125_52_2 Q2.hinj125_52_2
      Q2.hcardT125_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_52_2 i) (Q2.hfix125_52_2 i) _)
      colCert_125_52_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T125_52
      hfix125_52 hinj125_52 hcardT125_52
      (fun i => conj_mem_of_fixedPoints _ _ (T125_52 i) (hfix125_52 i) _)
      ⟨125, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T125_52_2 Q2.hfix125_52_2 Q2.hinj125_52_2
      Q2.hcardT125_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_52_2 i) (Q2.hfix125_52_2 i) _)
      colCert_125_52_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T125_52
      hfix125_52 hinj125_52 hcardT125_52
      (fun i => conj_mem_of_fixedPoints _ _ (T125_52 i) (hfix125_52 i) _)
      ⟨125, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T125_52_2 Q2.hfix125_52_2 Q2.hinj125_52_2
      Q2.hcardT125_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_52_2 i) (Q2.hfix125_52_2 i) _)
      colCert_125_52_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T125_52
      hfix125_52 hinj125_52 hcardT125_52
      (fun i => conj_mem_of_fixedPoints _ _ (T125_52 i) (hfix125_52 i) _)
      ⟨125, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T125_52_2 Q2.hfix125_52_2 Q2.hinj125_52_2
      Q2.hcardT125_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_52_2 i) (Q2.hfix125_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T125_52 = colFn colCertDiv_125_52_5.D1 (m := 5) from colCertDiv_125_52_5.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T125_52_2 = colFn colCertDiv_125_52_5.D2 (m := 5) from colCertDiv_125_52_5.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_52_5_match


theorem leaf_125_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T125_52
      hfix125_52 hinj125_52 hcardT125_52
      (fun i => conj_mem_of_fixedPoints _ _ (T125_52 i) (hfix125_52 i) _)
      ⟨125, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T125_52_2 Q2.hfix125_52_2 Q2.hinj125_52_2
      Q2.hcardT125_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_52_2 i) (Q2.hfix125_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T125_52 = colFn colCertDiv_125_52_10.D1 (m := 5) from colCertDiv_125_52_10.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T125_52_2 = colFn colCertDiv_125_52_10.D2 (m := 5) from colCertDiv_125_52_10.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_52_10_match


theorem leaf_125_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T125_52
      hfix125_52 hinj125_52 hcardT125_52
      (fun i => conj_mem_of_fixedPoints _ _ (T125_52 i) (hfix125_52 i) _)
      ⟨125, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T125_52_2 Q2.hfix125_52_2 Q2.hinj125_52_2
      Q2.hcardT125_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_52_2 i) (Q2.hfix125_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T125_52 = colFn colCertDiv_125_52_15.D1 (m := 5) from colCertDiv_125_52_15.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T125_52_2 = colFn colCertDiv_125_52_15.D2 (m := 5) from colCertDiv_125_52_15.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_52_15_match


theorem leaf_125_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T125_52
      hfix125_52 hinj125_52 hcardT125_52
      (fun i => conj_mem_of_fixedPoints _ _ (T125_52 i) (hfix125_52 i) _)
      ⟨125, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T125_52_2 Q2.hfix125_52_2 Q2.hinj125_52_2
      Q2.hcardT125_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_52_2 i) (Q2.hfix125_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T125_52 = colFn colCertDiv_125_52_20.D1 (m := 5) from colCertDiv_125_52_20.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T125_52_2 = colFn colCertDiv_125_52_20.D2 (m := 5) from colCertDiv_125_52_20.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_52_20_match


theorem leaf_125_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T125_53
      hfix125_53 hinj125_53 hcardT125_53
      (fun i => conj_mem_of_fixedPoints _ _ (T125_53 i) (hfix125_53 i) _)
      ⟨125, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T125_53_2 Q2.hfix125_53_2 Q2.hinj125_53_2
      Q2.hcardT125_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_53_2 i) (Q2.hfix125_53_2 i) _)
      colCert_125_53_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T125_53
      hfix125_53 hinj125_53 hcardT125_53
      (fun i => conj_mem_of_fixedPoints _ _ (T125_53 i) (hfix125_53 i) _)
      ⟨125, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T125_53_2 Q2.hfix125_53_2 Q2.hinj125_53_2
      Q2.hcardT125_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_53_2 i) (Q2.hfix125_53_2 i) _)
      colCert_125_53_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T125_53
      hfix125_53 hinj125_53 hcardT125_53
      (fun i => conj_mem_of_fixedPoints _ _ (T125_53 i) (hfix125_53 i) _)
      ⟨125, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T125_53_2 Q2.hfix125_53_2 Q2.hinj125_53_2
      Q2.hcardT125_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_53_2 i) (Q2.hfix125_53_2 i) _)
      colCert_125_53_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T125_53
      hfix125_53 hinj125_53 hcardT125_53
      (fun i => conj_mem_of_fixedPoints _ _ (T125_53 i) (hfix125_53 i) _)
      ⟨125, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T125_53_2 Q2.hfix125_53_2 Q2.hinj125_53_2
      Q2.hcardT125_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_53_2 i) (Q2.hfix125_53_2 i) _)
      colCert_125_53_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T125_53
      hfix125_53 hinj125_53 hcardT125_53
      (fun i => conj_mem_of_fixedPoints _ _ (T125_53 i) (hfix125_53 i) _)
      ⟨125, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T125_53_2 Q2.hfix125_53_2 Q2.hinj125_53_2
      Q2.hcardT125_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_53_2 i) (Q2.hfix125_53_2 i) _)
      colCert_125_53_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T125_53
      hfix125_53 hinj125_53 hcardT125_53
      (fun i => conj_mem_of_fixedPoints _ _ (T125_53 i) (hfix125_53 i) _)
      ⟨125, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T125_53_2 Q2.hfix125_53_2 Q2.hinj125_53_2
      Q2.hcardT125_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_53_2 i) (Q2.hfix125_53_2 i) _)
      colCert_125_53_5.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T125_53
      hfix125_53 hinj125_53 hcardT125_53
      (fun i => conj_mem_of_fixedPoints _ _ (T125_53 i) (hfix125_53 i) _)
      ⟨125, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T125_53_2 Q2.hfix125_53_2 Q2.hinj125_53_2
      Q2.hcardT125_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_53_2 i) (Q2.hfix125_53_2 i) _)
      colCert_125_53_10.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T125_53
      hfix125_53 hinj125_53 hcardT125_53
      (fun i => conj_mem_of_fixedPoints _ _ (T125_53 i) (hfix125_53 i) _)
      ⟨125, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T125_53_2 Q2.hfix125_53_2 Q2.hinj125_53_2
      Q2.hcardT125_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_53_2 i) (Q2.hfix125_53_2 i) _)
      colCert_125_53_15.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T125_53
      hfix125_53 hinj125_53 hcardT125_53
      (fun i => conj_mem_of_fixedPoints _ _ (T125_53 i) (hfix125_53 i) _)
      ⟨125, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T125_53_2 Q2.hfix125_53_2 Q2.hinj125_53_2
      Q2.hcardT125_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_53_2 i) (Q2.hfix125_53_2 i) _)
      colCert_125_53_20.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_81_0 (hp : 0 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp)) T125_81
      hfix125_81 hinj125_81 hcardT125_81
      (fun i => conj_mem_of_fixedPoints _ _ (T125_81 i) (hfix125_81 i) _)
      ⟨125, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 0 hp) Q2.T125_81_2 Q2.hfix125_81_2 Q2.hinj125_81_2
      Q2.hcardT125_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_81_2 i) (Q2.hfix125_81_2 i) _)
      colCert_125_81_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_81_1 (hp : 1 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp)) T125_81
      hfix125_81 hinj125_81 hcardT125_81
      (fun i => conj_mem_of_fixedPoints _ _ (T125_81 i) (hfix125_81 i) _)
      ⟨125, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 1 hp) Q2.T125_81_2 Q2.hfix125_81_2 Q2.hinj125_81_2
      Q2.hcardT125_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_81_2 i) (Q2.hfix125_81_2 i) _)
      colCert_125_81_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_81_2 (hp : 2 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp)) T125_81
      hfix125_81 hinj125_81 hcardT125_81
      (fun i => conj_mem_of_fixedPoints _ _ (T125_81 i) (hfix125_81 i) _)
      ⟨125, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 2 hp) Q2.T125_81_2 Q2.hfix125_81_2 Q2.hinj125_81_2
      Q2.hcardT125_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_81_2 i) (Q2.hfix125_81_2 i) _)
      colCert_125_81_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_81_3 (hp : 3 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp)) T125_81
      hfix125_81 hinj125_81 hcardT125_81
      (fun i => conj_mem_of_fixedPoints _ _ (T125_81 i) (hfix125_81 i) _)
      ⟨125, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 3 hp) Q2.T125_81_2 Q2.hfix125_81_2 Q2.hinj125_81_2
      Q2.hcardT125_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_81_2 i) (Q2.hfix125_81_2 i) _)
      colCert_125_81_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_81_4 (hp : 4 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp)) T125_81
      hfix125_81 hinj125_81 hcardT125_81
      (fun i => conj_mem_of_fixedPoints _ _ (T125_81 i) (hfix125_81 i) _)
      ⟨125, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 4 hp) Q2.T125_81_2 Q2.hfix125_81_2 Q2.hinj125_81_2
      Q2.hcardT125_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_81_2 i) (Q2.hfix125_81_2 i) _)
      colCert_125_81_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_81_5 (hp : 5 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp)) T125_81
      hfix125_81 hinj125_81 hcardT125_81
      (fun i => conj_mem_of_fixedPoints _ _ (T125_81 i) (hfix125_81 i) _)
      ⟨125, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 5 hp) Q2.T125_81_2 Q2.hfix125_81_2 Q2.hinj125_81_2
      Q2.hcardT125_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_81_2 i) (Q2.hfix125_81_2 i) _)
      colCert_125_81_5.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_81_10 (hp : 10 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp)) T125_81
      hfix125_81 hinj125_81 hcardT125_81
      (fun i => conj_mem_of_fixedPoints _ _ (T125_81 i) (hfix125_81 i) _)
      ⟨125, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 10 hp) Q2.T125_81_2 Q2.hfix125_81_2 Q2.hinj125_81_2
      Q2.hcardT125_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_81_2 i) (Q2.hfix125_81_2 i) _)
      colCert_125_81_10.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_81_15 (hp : 15 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp)) T125_81
      hfix125_81 hinj125_81 hcardT125_81
      (fun i => conj_mem_of_fixedPoints _ _ (T125_81 i) (hfix125_81 i) _)
      ⟨125, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 15 hp) Q2.T125_81_2 Q2.hfix125_81_2 Q2.hinj125_81_2
      Q2.hcardT125_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_81_2 i) (Q2.hfix125_81_2 i) _)
      colCert_125_81_15.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_81_20 (hp : 20 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp)) T125_81
      hfix125_81 hinj125_81 hcardT125_81
      (fun i => conj_mem_of_fixedPoints _ _ (T125_81 i) (hfix125_81 i) _)
      ⟨125, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 20 hp) Q2.T125_81_2 Q2.hfix125_81_2 Q2.hinj125_81_2
      Q2.hcardT125_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_81_2 i) (Q2.hfix125_81_2 i) _)
      colCert_125_81_20.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_93_0 (hp : 0 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 0 (transLenTr ⟨93, by decide⟩ 0 hp)) T125_93
      hfix125_93 hinj125_93 hcardT125_93
      (fun i => conj_mem_of_fixedPoints _ _ (T125_93 i) (hfix125_93 i) _)
      ⟨125, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 0 hp) Q2.T125_93_2 Q2.hfix125_93_2 Q2.hinj125_93_2
      Q2.hcardT125_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_93_2 i) (Q2.hfix125_93_2 i) _)
      colCert_125_93_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_93_1 (hp : 1 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 1 (transLenTr ⟨93, by decide⟩ 1 hp)) T125_93
      hfix125_93 hinj125_93 hcardT125_93
      (fun i => conj_mem_of_fixedPoints _ _ (T125_93 i) (hfix125_93 i) _)
      ⟨125, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 1 hp) Q2.T125_93_2 Q2.hfix125_93_2 Q2.hinj125_93_2
      Q2.hcardT125_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_93_2 i) (Q2.hfix125_93_2 i) _)
      colCert_125_93_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_93_2 (hp : 2 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 2 (transLenTr ⟨93, by decide⟩ 2 hp)) T125_93
      hfix125_93 hinj125_93 hcardT125_93
      (fun i => conj_mem_of_fixedPoints _ _ (T125_93 i) (hfix125_93 i) _)
      ⟨125, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 2 hp) Q2.T125_93_2 Q2.hfix125_93_2 Q2.hinj125_93_2
      Q2.hcardT125_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_93_2 i) (Q2.hfix125_93_2 i) _)
      colCert_125_93_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_93_3 (hp : 3 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 3 (transLenTr ⟨93, by decide⟩ 3 hp)) T125_93
      hfix125_93 hinj125_93 hcardT125_93
      (fun i => conj_mem_of_fixedPoints _ _ (T125_93 i) (hfix125_93 i) _)
      ⟨125, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 3 hp) Q2.T125_93_2 Q2.hfix125_93_2 Q2.hinj125_93_2
      Q2.hcardT125_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_93_2 i) (Q2.hfix125_93_2 i) _)
      colCert_125_93_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_93_4 (hp : 4 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 4 (transLenTr ⟨93, by decide⟩ 4 hp)) T125_93
      hfix125_93 hinj125_93 hcardT125_93
      (fun i => conj_mem_of_fixedPoints _ _ (T125_93 i) (hfix125_93 i) _)
      ⟨125, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 4 hp) Q2.T125_93_2 Q2.hfix125_93_2 Q2.hinj125_93_2
      Q2.hcardT125_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_93_2 i) (Q2.hfix125_93_2 i) _)
      colCert_125_93_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_93_5 (hp : 5 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 5 (transLenTr ⟨93, by decide⟩ 5 hp)) T125_93
      hfix125_93 hinj125_93 hcardT125_93
      (fun i => conj_mem_of_fixedPoints _ _ (T125_93 i) (hfix125_93 i) _)
      ⟨125, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 5 hp) Q2.T125_93_2 Q2.hfix125_93_2 Q2.hinj125_93_2
      Q2.hcardT125_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_93_2 i) (Q2.hfix125_93_2 i) _)
      colCert_125_93_5.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_93_10 (hp : 10 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp)) T125_93
      hfix125_93 hinj125_93 hcardT125_93
      (fun i => conj_mem_of_fixedPoints _ _ (T125_93 i) (hfix125_93 i) _)
      ⟨125, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 10 hp) Q2.T125_93_2 Q2.hfix125_93_2 Q2.hinj125_93_2
      Q2.hcardT125_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_93_2 i) (Q2.hfix125_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 10 (transLenTr ⟨93, by decide⟩ 10 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T125_93 = colFn colCertDiv_125_93_10.D1 (m := 5) from colCertDiv_125_93_10.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 10 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T125_93_2 = colFn colCertDiv_125_93_10.D2 (m := 5) from colCertDiv_125_93_10.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_93_10_match


theorem leaf_125_93_15 (hp : 15 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp)) T125_93
      hfix125_93 hinj125_93 hcardT125_93
      (fun i => conj_mem_of_fixedPoints _ _ (T125_93 i) (hfix125_93 i) _)
      ⟨125, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 15 hp) Q2.T125_93_2 Q2.hfix125_93_2 Q2.hinj125_93_2
      Q2.hcardT125_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_93_2 i) (Q2.hfix125_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 15 (transLenTr ⟨93, by decide⟩ 15 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T125_93 = colFn colCertDiv_125_93_15.D1 (m := 5) from colCertDiv_125_93_15.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 15 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T125_93_2 = colFn colCertDiv_125_93_15.D2 (m := 5) from colCertDiv_125_93_15.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_93_15_match


theorem leaf_125_93_20 (hp : 20 < (Q2.transData.getD 93 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨93, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp)) T125_93
      hfix125_93 hinj125_93 hcardT125_93
      (fun i => conj_mem_of_fixedPoints _ _ (T125_93 i) (hfix125_93 i) _)
      ⟨125, by decide⟩ ⟨93, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨93, by decide⟩ 20 hp) Q2.T125_93_2 Q2.hfix125_93_2 Q2.hinj125_93_2
      Q2.hcardT125_93_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_93_2 i) (Q2.hfix125_93_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨93, by decide⟩ 20 (transLenTr ⟨93, by decide⟩ 20 hp) : ↥(reps ⟨93, by decide⟩)) : Coordinate 1)
        T125_93 = colFn colCertDiv_125_93_20.D1 (m := 5) from colCertDiv_125_93_20.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨93, by decide⟩ 20 hp : ↥(Q2.reps ⟨93, by decide⟩)) : Coordinate 2)
        Q2.T125_93_2 = colFn colCertDiv_125_93_20.D2 (m := 5) from colCertDiv_125_93_20.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_93_20_match


theorem leaf_125_96_0 (hp : 0 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp)) T125_96
      hfix125_96 hinj125_96 hcardT125_96
      (fun i => conj_mem_of_fixedPoints _ _ (T125_96 i) (hfix125_96 i) _)
      ⟨125, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 0 hp) Q2.T125_96_2 Q2.hfix125_96_2 Q2.hinj125_96_2
      Q2.hcardT125_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_96_2 i) (Q2.hfix125_96_2 i) _)
      colCert_125_96_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_96_1 (hp : 1 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp)) T125_96
      hfix125_96 hinj125_96 hcardT125_96
      (fun i => conj_mem_of_fixedPoints _ _ (T125_96 i) (hfix125_96 i) _)
      ⟨125, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 1 hp) Q2.T125_96_2 Q2.hfix125_96_2 Q2.hinj125_96_2
      Q2.hcardT125_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_96_2 i) (Q2.hfix125_96_2 i) _)
      colCert_125_96_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_96_2 (hp : 2 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp)) T125_96
      hfix125_96 hinj125_96 hcardT125_96
      (fun i => conj_mem_of_fixedPoints _ _ (T125_96 i) (hfix125_96 i) _)
      ⟨125, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 2 hp) Q2.T125_96_2 Q2.hfix125_96_2 Q2.hinj125_96_2
      Q2.hcardT125_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_96_2 i) (Q2.hfix125_96_2 i) _)
      colCert_125_96_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_96_3 (hp : 3 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp)) T125_96
      hfix125_96 hinj125_96 hcardT125_96
      (fun i => conj_mem_of_fixedPoints _ _ (T125_96 i) (hfix125_96 i) _)
      ⟨125, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 3 hp) Q2.T125_96_2 Q2.hfix125_96_2 Q2.hinj125_96_2
      Q2.hcardT125_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_96_2 i) (Q2.hfix125_96_2 i) _)
      colCert_125_96_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_96_4 (hp : 4 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp)) T125_96
      hfix125_96 hinj125_96 hcardT125_96
      (fun i => conj_mem_of_fixedPoints _ _ (T125_96 i) (hfix125_96 i) _)
      ⟨125, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 4 hp) Q2.T125_96_2 Q2.hfix125_96_2 Q2.hinj125_96_2
      Q2.hcardT125_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_96_2 i) (Q2.hfix125_96_2 i) _)
      colCert_125_96_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_96_5 (hp : 5 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp)) T125_96
      hfix125_96 hinj125_96 hcardT125_96
      (fun i => conj_mem_of_fixedPoints _ _ (T125_96 i) (hfix125_96 i) _)
      ⟨125, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 5 hp) Q2.T125_96_2 Q2.hfix125_96_2 Q2.hinj125_96_2
      Q2.hcardT125_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_96_2 i) (Q2.hfix125_96_2 i) _)
      colCert_125_96_5.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_96_10 (hp : 10 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp)) T125_96
      hfix125_96 hinj125_96 hcardT125_96
      (fun i => conj_mem_of_fixedPoints _ _ (T125_96 i) (hfix125_96 i) _)
      ⟨125, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 10 hp) Q2.T125_96_2 Q2.hfix125_96_2 Q2.hinj125_96_2
      Q2.hcardT125_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_96_2 i) (Q2.hfix125_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T125_96 = colFn colCertDiv_125_96_10.D1 (m := 5) from colCertDiv_125_96_10.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 10 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T125_96_2 = colFn colCertDiv_125_96_10.D2 (m := 5) from colCertDiv_125_96_10.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_96_10_match


theorem leaf_125_96_15 (hp : 15 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp)) T125_96
      hfix125_96 hinj125_96 hcardT125_96
      (fun i => conj_mem_of_fixedPoints _ _ (T125_96 i) (hfix125_96 i) _)
      ⟨125, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 15 hp) Q2.T125_96_2 Q2.hfix125_96_2 Q2.hinj125_96_2
      Q2.hcardT125_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_96_2 i) (Q2.hfix125_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T125_96 = colFn colCertDiv_125_96_15.D1 (m := 5) from colCertDiv_125_96_15.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 15 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T125_96_2 = colFn colCertDiv_125_96_15.D2 (m := 5) from colCertDiv_125_96_15.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_96_15_match


theorem leaf_125_96_20 (hp : 20 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp)) T125_96
      hfix125_96 hinj125_96 hcardT125_96
      (fun i => conj_mem_of_fixedPoints _ _ (T125_96 i) (hfix125_96 i) _)
      ⟨125, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 20 hp) Q2.T125_96_2 Q2.hfix125_96_2 Q2.hinj125_96_2
      Q2.hcardT125_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_96_2 i) (Q2.hfix125_96_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp) : ↥(reps ⟨96, by decide⟩)) : Coordinate 1)
        T125_96 = colFn colCertDiv_125_96_20.D1 (m := 5) from colCertDiv_125_96_20.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨96, by decide⟩ 20 hp : ↥(Q2.reps ⟨96, by decide⟩)) : Coordinate 2)
        Q2.T125_96_2 = colFn colCertDiv_125_96_20.D2 (m := 5) from colCertDiv_125_96_20.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_96_20_match


theorem leaf_125_102_0 (hp : 0 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp)) T125_102
      hfix125_102 hinj125_102 hcardT125_102
      (fun i => conj_mem_of_fixedPoints _ _ (T125_102 i) (hfix125_102 i) _)
      ⟨125, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 0 hp) Q2.T125_102_2 Q2.hfix125_102_2 Q2.hinj125_102_2
      Q2.hcardT125_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_102_2 i) (Q2.hfix125_102_2 i) _)
      colCert_125_102_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_102_1 (hp : 1 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp)) T125_102
      hfix125_102 hinj125_102 hcardT125_102
      (fun i => conj_mem_of_fixedPoints _ _ (T125_102 i) (hfix125_102 i) _)
      ⟨125, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 1 hp) Q2.T125_102_2 Q2.hfix125_102_2 Q2.hinj125_102_2
      Q2.hcardT125_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_102_2 i) (Q2.hfix125_102_2 i) _)
      colCert_125_102_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_102_2 (hp : 2 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp)) T125_102
      hfix125_102 hinj125_102 hcardT125_102
      (fun i => conj_mem_of_fixedPoints _ _ (T125_102 i) (hfix125_102 i) _)
      ⟨125, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 2 hp) Q2.T125_102_2 Q2.hfix125_102_2 Q2.hinj125_102_2
      Q2.hcardT125_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_102_2 i) (Q2.hfix125_102_2 i) _)
      colCert_125_102_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_102_3 (hp : 3 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp)) T125_102
      hfix125_102 hinj125_102 hcardT125_102
      (fun i => conj_mem_of_fixedPoints _ _ (T125_102 i) (hfix125_102 i) _)
      ⟨125, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 3 hp) Q2.T125_102_2 Q2.hfix125_102_2 Q2.hinj125_102_2
      Q2.hcardT125_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_102_2 i) (Q2.hfix125_102_2 i) _)
      colCert_125_102_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_102_4 (hp : 4 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp)) T125_102
      hfix125_102 hinj125_102 hcardT125_102
      (fun i => conj_mem_of_fixedPoints _ _ (T125_102 i) (hfix125_102 i) _)
      ⟨125, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 4 hp) Q2.T125_102_2 Q2.hfix125_102_2 Q2.hinj125_102_2
      Q2.hcardT125_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_102_2 i) (Q2.hfix125_102_2 i) _)
      colCert_125_102_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_102_5 (hp : 5 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp)) T125_102
      hfix125_102 hinj125_102 hcardT125_102
      (fun i => conj_mem_of_fixedPoints _ _ (T125_102 i) (hfix125_102 i) _)
      ⟨125, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 5 hp) Q2.T125_102_2 Q2.hfix125_102_2 Q2.hinj125_102_2
      Q2.hcardT125_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_102_2 i) (Q2.hfix125_102_2 i) _)
      colCert_125_102_5.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_102_10 (hp : 10 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp)) T125_102
      hfix125_102 hinj125_102 hcardT125_102
      (fun i => conj_mem_of_fixedPoints _ _ (T125_102 i) (hfix125_102 i) _)
      ⟨125, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 10 hp) Q2.T125_102_2 Q2.hfix125_102_2 Q2.hinj125_102_2
      Q2.hcardT125_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_102_2 i) (Q2.hfix125_102_2 i) _)
      colCert_125_102_10.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_102_15 (hp : 15 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp)) T125_102
      hfix125_102 hinj125_102 hcardT125_102
      (fun i => conj_mem_of_fixedPoints _ _ (T125_102 i) (hfix125_102 i) _)
      ⟨125, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 15 hp) Q2.T125_102_2 Q2.hfix125_102_2 Q2.hinj125_102_2
      Q2.hcardT125_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_102_2 i) (Q2.hfix125_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T125_102 = colFn colCertDiv_125_102_15.D1 (m := 5) from colCertDiv_125_102_15.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 15 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T125_102_2 = colFn colCertDiv_125_102_15.D2 (m := 5) from colCertDiv_125_102_15.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_102_15_match


theorem leaf_125_102_20 (hp : 20 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨125, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp)) T125_102
      hfix125_102 hinj125_102 hcardT125_102
      (fun i => conj_mem_of_fixedPoints _ _ (T125_102 i) (hfix125_102 i) _)
      ⟨125, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 20 hp) Q2.T125_102_2 Q2.hfix125_102_2 Q2.hinj125_102_2
      Q2.hcardT125_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_102_2 i) (Q2.hfix125_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨125, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T125_102 = colFn colCertDiv_125_102_20.D1 (m := 5) from colCertDiv_125_102_20.bind1,
    show colData2 (⟨125, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 20 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T125_102_2 = colFn colCertDiv_125_102_20.D2 (m := 5) from colCertDiv_125_102_20.bind2]
  rw [alnId_125 j hj]
  exact fastcode_of_div ⟨125, by decide⟩ _ _ _
    ((alnId_125 j hj) ▸ Q2.listedAt (⟨125, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨125, by decide⟩ : Fin 148) hj hq).1) colCertDiv_125_102_20_match


theorem leaf_125_105_0 (hp : 0 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 0 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_1 (hp : 1 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 1 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_2 (hp : 2 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 2 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_3 (hp : 3 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 3 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_4 (hp : 4 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 4 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_5 (hp : 5 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 5 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_5.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_10 (hp : 10 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 10 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_10.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_15 (hp : 15 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 15 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_15.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_20 (hp : 20 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 20 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_20.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_25 (hp : 25 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 25 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 25 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_25.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_50 (hp : 50 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 50 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 50 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_50.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_75 (hp : 75 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 75 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 75 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_75.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_105_100 (hp : 100 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 100 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp)) T125_105
      hfix125_105 hinj125_105 hcardT125_105
      (fun i => conj_mem_of_fixedPoints _ _ (T125_105 i) (hfix125_105 i) _)
      ⟨125, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 100 hp) Q2.T125_105_2 Q2.hfix125_105_2 Q2.hinj125_105_2
      Q2.hcardT125_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_105_2 i) (Q2.hfix125_105_2 i) _)
      colCert_125_105_100.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_114_0 (hp : 0 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp)) T125_114
      hfix125_114 hinj125_114 hcardT125_114
      (fun i => conj_mem_of_fixedPoints _ _ (T125_114 i) (hfix125_114 i) _)
      ⟨125, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 0 hp) Q2.T125_114_2 Q2.hfix125_114_2 Q2.hinj125_114_2
      Q2.hcardT125_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_114_2 i) (Q2.hfix125_114_2 i) _)
      colCert_125_114_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_114_1 (hp : 1 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp)) T125_114
      hfix125_114 hinj125_114 hcardT125_114
      (fun i => conj_mem_of_fixedPoints _ _ (T125_114 i) (hfix125_114 i) _)
      ⟨125, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 1 hp) Q2.T125_114_2 Q2.hfix125_114_2 Q2.hinj125_114_2
      Q2.hcardT125_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_114_2 i) (Q2.hfix125_114_2 i) _)
      colCert_125_114_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_114_2 (hp : 2 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp)) T125_114
      hfix125_114 hinj125_114 hcardT125_114
      (fun i => conj_mem_of_fixedPoints _ _ (T125_114 i) (hfix125_114 i) _)
      ⟨125, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 2 hp) Q2.T125_114_2 Q2.hfix125_114_2 Q2.hinj125_114_2
      Q2.hcardT125_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_114_2 i) (Q2.hfix125_114_2 i) _)
      colCert_125_114_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_114_3 (hp : 3 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp)) T125_114
      hfix125_114 hinj125_114 hcardT125_114
      (fun i => conj_mem_of_fixedPoints _ _ (T125_114 i) (hfix125_114 i) _)
      ⟨125, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 3 hp) Q2.T125_114_2 Q2.hfix125_114_2 Q2.hinj125_114_2
      Q2.hcardT125_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_114_2 i) (Q2.hfix125_114_2 i) _)
      colCert_125_114_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_114_4 (hp : 4 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp)) T125_114
      hfix125_114 hinj125_114 hcardT125_114
      (fun i => conj_mem_of_fixedPoints _ _ (T125_114 i) (hfix125_114 i) _)
      ⟨125, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 4 hp) Q2.T125_114_2 Q2.hfix125_114_2 Q2.hinj125_114_2
      Q2.hcardT125_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_114_2 i) (Q2.hfix125_114_2 i) _)
      colCert_125_114_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_114_5 (hp : 5 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp)) T125_114
      hfix125_114 hinj125_114 hcardT125_114
      (fun i => conj_mem_of_fixedPoints _ _ (T125_114 i) (hfix125_114 i) _)
      ⟨125, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 5 hp) Q2.T125_114_2 Q2.hfix125_114_2 Q2.hinj125_114_2
      Q2.hcardT125_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_114_2 i) (Q2.hfix125_114_2 i) _)
      colCert_125_114_5.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_114_10 (hp : 10 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp)) T125_114
      hfix125_114 hinj125_114 hcardT125_114
      (fun i => conj_mem_of_fixedPoints _ _ (T125_114 i) (hfix125_114 i) _)
      ⟨125, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 10 hp) Q2.T125_114_2 Q2.hfix125_114_2 Q2.hinj125_114_2
      Q2.hcardT125_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_114_2 i) (Q2.hfix125_114_2 i) _)
      colCert_125_114_10.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_114_15 (hp : 15 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp)) T125_114
      hfix125_114 hinj125_114 hcardT125_114
      (fun i => conj_mem_of_fixedPoints _ _ (T125_114 i) (hfix125_114 i) _)
      ⟨125, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 15 hp) Q2.T125_114_2 Q2.hfix125_114_2 Q2.hinj125_114_2
      Q2.hcardT125_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_114_2 i) (Q2.hfix125_114_2 i) _)
      colCert_125_114_15.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_114_20 (hp : 20 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp)) T125_114
      hfix125_114 hinj125_114 hcardT125_114
      (fun i => conj_mem_of_fixedPoints _ _ (T125_114 i) (hfix125_114 i) _)
      ⟨125, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 20 hp) Q2.T125_114_2 Q2.hfix125_114_2 Q2.hinj125_114_2
      Q2.hcardT125_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_114_2 i) (Q2.hfix125_114_2 i) _)
      colCert_125_114_20.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_0 (hp : 0 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 0 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 0 (transLenTr ⟨125, by decide⟩ 0 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 0 (transLenTr ⟨125, by decide⟩ 0 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 0 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_0.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_1 (hp : 1 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 1 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 1 (transLenTr ⟨125, by decide⟩ 1 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 1 (transLenTr ⟨125, by decide⟩ 1 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 1 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_1.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_2 (hp : 2 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 2 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 2 (transLenTr ⟨125, by decide⟩ 2 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 2 (transLenTr ⟨125, by decide⟩ 2 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 2 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_2.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_3 (hp : 3 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 3 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 3 (transLenTr ⟨125, by decide⟩ 3 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 3 (transLenTr ⟨125, by decide⟩ 3 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 3 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_3.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_4 (hp : 4 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 4 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 4 (transLenTr ⟨125, by decide⟩ 4 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 4 (transLenTr ⟨125, by decide⟩ 4 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 4 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_4.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_5 (hp : 5 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 5 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 5 (transLenTr ⟨125, by decide⟩ 5 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 5 (transLenTr ⟨125, by decide⟩ 5 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 5 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_5.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_6 (hp : 6 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 6 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 6 (transLenTr ⟨125, by decide⟩ 6 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 6 (transLenTr ⟨125, by decide⟩ 6 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 6 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_6.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_7 (hp : 7 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 7 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 7 (transLenTr ⟨125, by decide⟩ 7 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 7 (transLenTr ⟨125, by decide⟩ 7 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 7 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_7.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_8 (hp : 8 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 8 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 8 (transLenTr ⟨125, by decide⟩ 8 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 8 (transLenTr ⟨125, by decide⟩ 8 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 8 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_8.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_9 (hp : 9 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 9 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 9 (transLenTr ⟨125, by decide⟩ 9 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 9 (transLenTr ⟨125, by decide⟩ 9 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 9 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_9.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_10 (hp : 10 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 10 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 10 (transLenTr ⟨125, by decide⟩ 10 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 10 (transLenTr ⟨125, by decide⟩ 10 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 10 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_10.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_11 (hp : 11 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 11 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 11 (transLenTr ⟨125, by decide⟩ 11 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 11 (transLenTr ⟨125, by decide⟩ 11 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 11 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_11.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_12 (hp : 12 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 12 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 12 (transLenTr ⟨125, by decide⟩ 12 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 12 (transLenTr ⟨125, by decide⟩ 12 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 12 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_12.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_13 (hp : 13 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 13 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 13 (transLenTr ⟨125, by decide⟩ 13 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 13 (transLenTr ⟨125, by decide⟩ 13 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 13 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_13.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_14 (hp : 14 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 14 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 14 (transLenTr ⟨125, by decide⟩ 14 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 14 (transLenTr ⟨125, by decide⟩ 14 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 14 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_14.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_15 (hp : 15 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 15 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 15 (transLenTr ⟨125, by decide⟩ 15 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 15 (transLenTr ⟨125, by decide⟩ 15 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 15 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_15.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_16 (hp : 16 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 16 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 16 (transLenTr ⟨125, by decide⟩ 16 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 16 (transLenTr ⟨125, by decide⟩ 16 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 16 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_16.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_17 (hp : 17 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 17 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 17 (transLenTr ⟨125, by decide⟩ 17 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 17 (transLenTr ⟨125, by decide⟩ 17 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 17 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_17.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_18 (hp : 18 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 18 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 18 (transLenTr ⟨125, by decide⟩ 18 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 18 (transLenTr ⟨125, by decide⟩ 18 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 18 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_18.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_19 (hp : 19 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 19 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 19 (transLenTr ⟨125, by decide⟩ 19 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 19 (transLenTr ⟨125, by decide⟩ 19 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 19 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_19.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_20 (hp : 20 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 20 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 20 (transLenTr ⟨125, by decide⟩ 20 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 20 (transLenTr ⟨125, by decide⟩ 20 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 20 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_20.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_21 (hp : 21 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 21 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 21 (transLenTr ⟨125, by decide⟩ 21 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 21 (transLenTr ⟨125, by decide⟩ 21 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 21 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_21.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_22 (hp : 22 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 22 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 22 (transLenTr ⟨125, by decide⟩ 22 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 22 (transLenTr ⟨125, by decide⟩ 22 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 22 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_22.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_23 (hp : 23 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 23 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 23 (transLenTr ⟨125, by decide⟩ 23 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 23 (transLenTr ⟨125, by decide⟩ 23 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 23 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_23.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_125_125_24 (hp : 24 < (Q2.transData.getD 125 []).length)
    (j : Nat) (hj : j < (repChars.getD 125 []).length)
    (hq : (normIsRep.getD 125 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ 24 hp)
        (rowE2 (⟨125, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ 24 (transLenTr ⟨125, by decide⟩ 24 hp))
        (rowE1 (⟨125, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨125, by decide⟩ : Fin 148) ⟨125, by decide⟩ _
      (validAt ⟨125, by decide⟩ (listedAt ⟨125, by decide⟩ hj))
      (colE1 ⟨125, by decide⟩ 24 (transLenTr ⟨125, by decide⟩ 24 hp)) T125_125
      hfix125_125 hinj125_125 hcardT125_125
      (fun i => conj_mem_of_fixedPoints _ _ (T125_125 i) (hfix125_125 i) _)
      ⟨125, by decide⟩ ⟨125, by decide⟩ _
      (Q2.validAt ⟨125, by decide⟩ (Q2.listedAt ⟨125, by decide⟩
        (alnCheck_rep ⟨125, by decide⟩ hj hq).1))
      (colE2 ⟨125, by decide⟩ 24 hp) Q2.T125_125_2 Q2.hfix125_125_2 Q2.hinj125_125_2
      Q2.hcardT125_125_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T125_125_2 i) (Q2.hfix125_125_2 i) _)
      colCert_125_125_24.hD ?_).symm
  rw [alnId_125 j hj]


theorem leaf_126_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T126_3
      hfix126_3 hinj126_3 hcardT126_3
      (fun i => conj_mem_of_fixedPoints _ _ (T126_3 i) (hfix126_3 i) _)
      ⟨126, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T126_3_2 Q2.hfix126_3_2 Q2.hinj126_3_2
      Q2.hcardT126_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_3_2 i) (Q2.hfix126_3_2 i) _)
      colCert_126_3_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T126_3
      hfix126_3 hinj126_3 hcardT126_3
      (fun i => conj_mem_of_fixedPoints _ _ (T126_3 i) (hfix126_3 i) _)
      ⟨126, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T126_3_2 Q2.hfix126_3_2 Q2.hinj126_3_2
      Q2.hcardT126_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_3_2 i) (Q2.hfix126_3_2 i) _)
      colCert_126_3_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T126_3
      hfix126_3 hinj126_3 hcardT126_3
      (fun i => conj_mem_of_fixedPoints _ _ (T126_3 i) (hfix126_3 i) _)
      ⟨126, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T126_3_2 Q2.hfix126_3_2 Q2.hinj126_3_2
      Q2.hcardT126_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_3_2 i) (Q2.hfix126_3_2 i) _)
      colCert_126_3_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T126_3
      hfix126_3 hinj126_3 hcardT126_3
      (fun i => conj_mem_of_fixedPoints _ _ (T126_3 i) (hfix126_3 i) _)
      ⟨126, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T126_3_2 Q2.hfix126_3_2 Q2.hinj126_3_2
      Q2.hcardT126_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_3_2 i) (Q2.hfix126_3_2 i) _)
      colCert_126_3_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T126_3
      hfix126_3 hinj126_3 hcardT126_3
      (fun i => conj_mem_of_fixedPoints _ _ (T126_3 i) (hfix126_3 i) _)
      ⟨126, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T126_3_2 Q2.hfix126_3_2 Q2.hinj126_3_2
      Q2.hcardT126_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_3_2 i) (Q2.hfix126_3_2 i) _)
      colCert_126_3_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T126_10
      hfix126_10 hinj126_10 hcardT126_10
      (fun i => conj_mem_of_fixedPoints _ _ (T126_10 i) (hfix126_10 i) _)
      ⟨126, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T126_10_2 Q2.hfix126_10_2 Q2.hinj126_10_2
      Q2.hcardT126_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_10_2 i) (Q2.hfix126_10_2 i) _)
      colCert_126_10_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T126_10
      hfix126_10 hinj126_10 hcardT126_10
      (fun i => conj_mem_of_fixedPoints _ _ (T126_10 i) (hfix126_10 i) _)
      ⟨126, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T126_10_2 Q2.hfix126_10_2 Q2.hinj126_10_2
      Q2.hcardT126_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_10_2 i) (Q2.hfix126_10_2 i) _)
      colCert_126_10_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T126_10
      hfix126_10 hinj126_10 hcardT126_10
      (fun i => conj_mem_of_fixedPoints _ _ (T126_10 i) (hfix126_10 i) _)
      ⟨126, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T126_10_2 Q2.hfix126_10_2 Q2.hinj126_10_2
      Q2.hcardT126_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_10_2 i) (Q2.hfix126_10_2 i) _)
      colCert_126_10_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T126_10
      hfix126_10 hinj126_10 hcardT126_10
      (fun i => conj_mem_of_fixedPoints _ _ (T126_10 i) (hfix126_10 i) _)
      ⟨126, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T126_10_2 Q2.hfix126_10_2 Q2.hinj126_10_2
      Q2.hcardT126_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_10_2 i) (Q2.hfix126_10_2 i) _)
      colCert_126_10_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T126_10
      hfix126_10 hinj126_10 hcardT126_10
      (fun i => conj_mem_of_fixedPoints _ _ (T126_10 i) (hfix126_10 i) _)
      ⟨126, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T126_10_2 Q2.hfix126_10_2 Q2.hinj126_10_2
      Q2.hcardT126_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_10_2 i) (Q2.hfix126_10_2 i) _)
      colCert_126_10_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T126_12
      hfix126_12 hinj126_12 hcardT126_12
      (fun i => conj_mem_of_fixedPoints _ _ (T126_12 i) (hfix126_12 i) _)
      ⟨126, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T126_12_2 Q2.hfix126_12_2 Q2.hinj126_12_2
      Q2.hcardT126_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_12_2 i) (Q2.hfix126_12_2 i) _)
      colCert_126_12_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T126_12
      hfix126_12 hinj126_12 hcardT126_12
      (fun i => conj_mem_of_fixedPoints _ _ (T126_12 i) (hfix126_12 i) _)
      ⟨126, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T126_12_2 Q2.hfix126_12_2 Q2.hinj126_12_2
      Q2.hcardT126_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_12_2 i) (Q2.hfix126_12_2 i) _)
      colCert_126_12_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T126_12
      hfix126_12 hinj126_12 hcardT126_12
      (fun i => conj_mem_of_fixedPoints _ _ (T126_12 i) (hfix126_12 i) _)
      ⟨126, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T126_12_2 Q2.hfix126_12_2 Q2.hinj126_12_2
      Q2.hcardT126_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_12_2 i) (Q2.hfix126_12_2 i) _)
      colCert_126_12_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T126_12
      hfix126_12 hinj126_12 hcardT126_12
      (fun i => conj_mem_of_fixedPoints _ _ (T126_12 i) (hfix126_12 i) _)
      ⟨126, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T126_12_2 Q2.hfix126_12_2 Q2.hinj126_12_2
      Q2.hcardT126_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_12_2 i) (Q2.hfix126_12_2 i) _)
      colCert_126_12_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T126_12
      hfix126_12 hinj126_12 hcardT126_12
      (fun i => conj_mem_of_fixedPoints _ _ (T126_12 i) (hfix126_12 i) _)
      ⟨126, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T126_12_2 Q2.hfix126_12_2 Q2.hinj126_12_2
      Q2.hcardT126_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_12_2 i) (Q2.hfix126_12_2 i) _)
      colCert_126_12_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T126_21
      hfix126_21 hinj126_21 hcardT126_21
      (fun i => conj_mem_of_fixedPoints _ _ (T126_21 i) (hfix126_21 i) _)
      ⟨126, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T126_21_2 Q2.hfix126_21_2 Q2.hinj126_21_2
      Q2.hcardT126_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_21_2 i) (Q2.hfix126_21_2 i) _)
      colCert_126_21_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T126_21
      hfix126_21 hinj126_21 hcardT126_21
      (fun i => conj_mem_of_fixedPoints _ _ (T126_21 i) (hfix126_21 i) _)
      ⟨126, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T126_21_2 Q2.hfix126_21_2 Q2.hinj126_21_2
      Q2.hcardT126_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_21_2 i) (Q2.hfix126_21_2 i) _)
      colCert_126_21_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T126_21
      hfix126_21 hinj126_21 hcardT126_21
      (fun i => conj_mem_of_fixedPoints _ _ (T126_21 i) (hfix126_21 i) _)
      ⟨126, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T126_21_2 Q2.hfix126_21_2 Q2.hinj126_21_2
      Q2.hcardT126_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_21_2 i) (Q2.hfix126_21_2 i) _)
      colCert_126_21_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T126_21
      hfix126_21 hinj126_21 hcardT126_21
      (fun i => conj_mem_of_fixedPoints _ _ (T126_21 i) (hfix126_21 i) _)
      ⟨126, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T126_21_2 Q2.hfix126_21_2 Q2.hinj126_21_2
      Q2.hcardT126_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_21_2 i) (Q2.hfix126_21_2 i) _)
      colCert_126_21_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T126_21
      hfix126_21 hinj126_21 hcardT126_21
      (fun i => conj_mem_of_fixedPoints _ _ (T126_21 i) (hfix126_21 i) _)
      ⟨126, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T126_21_2 Q2.hfix126_21_2 Q2.hinj126_21_2
      Q2.hcardT126_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_21_2 i) (Q2.hfix126_21_2 i) _)
      colCert_126_21_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T126_21
      hfix126_21 hinj126_21 hcardT126_21
      (fun i => conj_mem_of_fixedPoints _ _ (T126_21 i) (hfix126_21 i) _)
      ⟨126, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T126_21_2 Q2.hfix126_21_2 Q2.hinj126_21_2
      Q2.hcardT126_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_21_2 i) (Q2.hfix126_21_2 i) _)
      colCert_126_21_5.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T126_21
      hfix126_21 hinj126_21 hcardT126_21
      (fun i => conj_mem_of_fixedPoints _ _ (T126_21 i) (hfix126_21 i) _)
      ⟨126, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T126_21_2 Q2.hfix126_21_2 Q2.hinj126_21_2
      Q2.hcardT126_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_21_2 i) (Q2.hfix126_21_2 i) _)
      colCert_126_21_10.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T126_21
      hfix126_21 hinj126_21 hcardT126_21
      (fun i => conj_mem_of_fixedPoints _ _ (T126_21 i) (hfix126_21 i) _)
      ⟨126, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T126_21_2 Q2.hfix126_21_2 Q2.hinj126_21_2
      Q2.hcardT126_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_21_2 i) (Q2.hfix126_21_2 i) _)
      colCert_126_21_15.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T126_21
      hfix126_21 hinj126_21 hcardT126_21
      (fun i => conj_mem_of_fixedPoints _ _ (T126_21 i) (hfix126_21 i) _)
      ⟨126, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T126_21_2 Q2.hfix126_21_2 Q2.hinj126_21_2
      Q2.hcardT126_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_21_2 i) (Q2.hfix126_21_2 i) _)
      colCert_126_21_20.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T126_31
      hfix126_31 hinj126_31 hcardT126_31
      (fun i => conj_mem_of_fixedPoints _ _ (T126_31 i) (hfix126_31 i) _)
      ⟨126, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T126_31_2 Q2.hfix126_31_2 Q2.hinj126_31_2
      Q2.hcardT126_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_31_2 i) (Q2.hfix126_31_2 i) _)
      colCert_126_31_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T126_31
      hfix126_31 hinj126_31 hcardT126_31
      (fun i => conj_mem_of_fixedPoints _ _ (T126_31 i) (hfix126_31 i) _)
      ⟨126, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T126_31_2 Q2.hfix126_31_2 Q2.hinj126_31_2
      Q2.hcardT126_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_31_2 i) (Q2.hfix126_31_2 i) _)
      colCert_126_31_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T126_31
      hfix126_31 hinj126_31 hcardT126_31
      (fun i => conj_mem_of_fixedPoints _ _ (T126_31 i) (hfix126_31 i) _)
      ⟨126, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T126_31_2 Q2.hfix126_31_2 Q2.hinj126_31_2
      Q2.hcardT126_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_31_2 i) (Q2.hfix126_31_2 i) _)
      colCert_126_31_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T126_31
      hfix126_31 hinj126_31 hcardT126_31
      (fun i => conj_mem_of_fixedPoints _ _ (T126_31 i) (hfix126_31 i) _)
      ⟨126, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T126_31_2 Q2.hfix126_31_2 Q2.hinj126_31_2
      Q2.hcardT126_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_31_2 i) (Q2.hfix126_31_2 i) _)
      colCert_126_31_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T126_31
      hfix126_31 hinj126_31 hcardT126_31
      (fun i => conj_mem_of_fixedPoints _ _ (T126_31 i) (hfix126_31 i) _)
      ⟨126, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T126_31_2 Q2.hfix126_31_2 Q2.hinj126_31_2
      Q2.hcardT126_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_31_2 i) (Q2.hfix126_31_2 i) _)
      colCert_126_31_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T126_31
      hfix126_31 hinj126_31 hcardT126_31
      (fun i => conj_mem_of_fixedPoints _ _ (T126_31 i) (hfix126_31 i) _)
      ⟨126, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T126_31_2 Q2.hfix126_31_2 Q2.hinj126_31_2
      Q2.hcardT126_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_31_2 i) (Q2.hfix126_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T126_31 = colFn colCertDiv_126_31_5.D1 (m := 5) from colCertDiv_126_31_5.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 5 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T126_31_2 = colFn colCertDiv_126_31_5.D2 (m := 5) from colCertDiv_126_31_5.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_31_5_match


theorem leaf_126_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T126_31
      hfix126_31 hinj126_31 hcardT126_31
      (fun i => conj_mem_of_fixedPoints _ _ (T126_31 i) (hfix126_31 i) _)
      ⟨126, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T126_31_2 Q2.hfix126_31_2 Q2.hinj126_31_2
      Q2.hcardT126_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_31_2 i) (Q2.hfix126_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T126_31 = colFn colCertDiv_126_31_10.D1 (m := 5) from colCertDiv_126_31_10.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 10 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T126_31_2 = colFn colCertDiv_126_31_10.D2 (m := 5) from colCertDiv_126_31_10.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_31_10_match


theorem leaf_126_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T126_31
      hfix126_31 hinj126_31 hcardT126_31
      (fun i => conj_mem_of_fixedPoints _ _ (T126_31 i) (hfix126_31 i) _)
      ⟨126, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T126_31_2 Q2.hfix126_31_2 Q2.hinj126_31_2
      Q2.hcardT126_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_31_2 i) (Q2.hfix126_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T126_31 = colFn colCertDiv_126_31_15.D1 (m := 5) from colCertDiv_126_31_15.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 15 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T126_31_2 = colFn colCertDiv_126_31_15.D2 (m := 5) from colCertDiv_126_31_15.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_31_15_match


theorem leaf_126_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T126_31
      hfix126_31 hinj126_31 hcardT126_31
      (fun i => conj_mem_of_fixedPoints _ _ (T126_31 i) (hfix126_31 i) _)
      ⟨126, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T126_31_2 Q2.hfix126_31_2 Q2.hinj126_31_2
      Q2.hcardT126_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_31_2 i) (Q2.hfix126_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T126_31 = colFn colCertDiv_126_31_20.D1 (m := 5) from colCertDiv_126_31_20.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 20 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T126_31_2 = colFn colCertDiv_126_31_20.D2 (m := 5) from colCertDiv_126_31_20.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_31_20_match


theorem leaf_126_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T126_37
      hfix126_37 hinj126_37 hcardT126_37
      (fun i => conj_mem_of_fixedPoints _ _ (T126_37 i) (hfix126_37 i) _)
      ⟨126, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T126_37_2 Q2.hfix126_37_2 Q2.hinj126_37_2
      Q2.hcardT126_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_37_2 i) (Q2.hfix126_37_2 i) _)
      colCert_126_37_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T126_37
      hfix126_37 hinj126_37 hcardT126_37
      (fun i => conj_mem_of_fixedPoints _ _ (T126_37 i) (hfix126_37 i) _)
      ⟨126, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T126_37_2 Q2.hfix126_37_2 Q2.hinj126_37_2
      Q2.hcardT126_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_37_2 i) (Q2.hfix126_37_2 i) _)
      colCert_126_37_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T126_37
      hfix126_37 hinj126_37 hcardT126_37
      (fun i => conj_mem_of_fixedPoints _ _ (T126_37 i) (hfix126_37 i) _)
      ⟨126, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T126_37_2 Q2.hfix126_37_2 Q2.hinj126_37_2
      Q2.hcardT126_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_37_2 i) (Q2.hfix126_37_2 i) _)
      colCert_126_37_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T126_37
      hfix126_37 hinj126_37 hcardT126_37
      (fun i => conj_mem_of_fixedPoints _ _ (T126_37 i) (hfix126_37 i) _)
      ⟨126, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T126_37_2 Q2.hfix126_37_2 Q2.hinj126_37_2
      Q2.hcardT126_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_37_2 i) (Q2.hfix126_37_2 i) _)
      colCert_126_37_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T126_37
      hfix126_37 hinj126_37 hcardT126_37
      (fun i => conj_mem_of_fixedPoints _ _ (T126_37 i) (hfix126_37 i) _)
      ⟨126, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T126_37_2 Q2.hfix126_37_2 Q2.hinj126_37_2
      Q2.hcardT126_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_37_2 i) (Q2.hfix126_37_2 i) _)
      colCert_126_37_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T126_37
      hfix126_37 hinj126_37 hcardT126_37
      (fun i => conj_mem_of_fixedPoints _ _ (T126_37 i) (hfix126_37 i) _)
      ⟨126, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T126_37_2 Q2.hfix126_37_2 Q2.hinj126_37_2
      Q2.hcardT126_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_37_2 i) (Q2.hfix126_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T126_37 = colFn colCertDiv_126_37_5.D1 (m := 5) from colCertDiv_126_37_5.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T126_37_2 = colFn colCertDiv_126_37_5.D2 (m := 5) from colCertDiv_126_37_5.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_37_5_match


theorem leaf_126_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T126_37
      hfix126_37 hinj126_37 hcardT126_37
      (fun i => conj_mem_of_fixedPoints _ _ (T126_37 i) (hfix126_37 i) _)
      ⟨126, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T126_37_2 Q2.hfix126_37_2 Q2.hinj126_37_2
      Q2.hcardT126_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_37_2 i) (Q2.hfix126_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T126_37 = colFn colCertDiv_126_37_10.D1 (m := 5) from colCertDiv_126_37_10.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T126_37_2 = colFn colCertDiv_126_37_10.D2 (m := 5) from colCertDiv_126_37_10.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_37_10_match


theorem leaf_126_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T126_37
      hfix126_37 hinj126_37 hcardT126_37
      (fun i => conj_mem_of_fixedPoints _ _ (T126_37 i) (hfix126_37 i) _)
      ⟨126, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T126_37_2 Q2.hfix126_37_2 Q2.hinj126_37_2
      Q2.hcardT126_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_37_2 i) (Q2.hfix126_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T126_37 = colFn colCertDiv_126_37_15.D1 (m := 5) from colCertDiv_126_37_15.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T126_37_2 = colFn colCertDiv_126_37_15.D2 (m := 5) from colCertDiv_126_37_15.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_37_15_match


theorem leaf_126_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T126_37
      hfix126_37 hinj126_37 hcardT126_37
      (fun i => conj_mem_of_fixedPoints _ _ (T126_37 i) (hfix126_37 i) _)
      ⟨126, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T126_37_2 Q2.hfix126_37_2 Q2.hinj126_37_2
      Q2.hcardT126_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_37_2 i) (Q2.hfix126_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T126_37 = colFn colCertDiv_126_37_20.D1 (m := 5) from colCertDiv_126_37_20.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T126_37_2 = colFn colCertDiv_126_37_20.D2 (m := 5) from colCertDiv_126_37_20.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_37_20_match


theorem leaf_126_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T126_39
      hfix126_39 hinj126_39 hcardT126_39
      (fun i => conj_mem_of_fixedPoints _ _ (T126_39 i) (hfix126_39 i) _)
      ⟨126, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T126_39_2 Q2.hfix126_39_2 Q2.hinj126_39_2
      Q2.hcardT126_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_39_2 i) (Q2.hfix126_39_2 i) _)
      colCert_126_39_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T126_39
      hfix126_39 hinj126_39 hcardT126_39
      (fun i => conj_mem_of_fixedPoints _ _ (T126_39 i) (hfix126_39 i) _)
      ⟨126, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T126_39_2 Q2.hfix126_39_2 Q2.hinj126_39_2
      Q2.hcardT126_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_39_2 i) (Q2.hfix126_39_2 i) _)
      colCert_126_39_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T126_39
      hfix126_39 hinj126_39 hcardT126_39
      (fun i => conj_mem_of_fixedPoints _ _ (T126_39 i) (hfix126_39 i) _)
      ⟨126, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T126_39_2 Q2.hfix126_39_2 Q2.hinj126_39_2
      Q2.hcardT126_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_39_2 i) (Q2.hfix126_39_2 i) _)
      colCert_126_39_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T126_39
      hfix126_39 hinj126_39 hcardT126_39
      (fun i => conj_mem_of_fixedPoints _ _ (T126_39 i) (hfix126_39 i) _)
      ⟨126, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T126_39_2 Q2.hfix126_39_2 Q2.hinj126_39_2
      Q2.hcardT126_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_39_2 i) (Q2.hfix126_39_2 i) _)
      colCert_126_39_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T126_39
      hfix126_39 hinj126_39 hcardT126_39
      (fun i => conj_mem_of_fixedPoints _ _ (T126_39 i) (hfix126_39 i) _)
      ⟨126, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T126_39_2 Q2.hfix126_39_2 Q2.hinj126_39_2
      Q2.hcardT126_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_39_2 i) (Q2.hfix126_39_2 i) _)
      colCert_126_39_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T126_39
      hfix126_39 hinj126_39 hcardT126_39
      (fun i => conj_mem_of_fixedPoints _ _ (T126_39 i) (hfix126_39 i) _)
      ⟨126, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T126_39_2 Q2.hfix126_39_2 Q2.hinj126_39_2
      Q2.hcardT126_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_39_2 i) (Q2.hfix126_39_2 i) _)
      colCert_126_39_5.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T126_39
      hfix126_39 hinj126_39 hcardT126_39
      (fun i => conj_mem_of_fixedPoints _ _ (T126_39 i) (hfix126_39 i) _)
      ⟨126, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T126_39_2 Q2.hfix126_39_2 Q2.hinj126_39_2
      Q2.hcardT126_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_39_2 i) (Q2.hfix126_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T126_39 = colFn colCertDiv_126_39_10.D1 (m := 5) from colCertDiv_126_39_10.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 10 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T126_39_2 = colFn colCertDiv_126_39_10.D2 (m := 5) from colCertDiv_126_39_10.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_39_10_match


theorem leaf_126_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T126_39
      hfix126_39 hinj126_39 hcardT126_39
      (fun i => conj_mem_of_fixedPoints _ _ (T126_39 i) (hfix126_39 i) _)
      ⟨126, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T126_39_2 Q2.hfix126_39_2 Q2.hinj126_39_2
      Q2.hcardT126_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_39_2 i) (Q2.hfix126_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T126_39 = colFn colCertDiv_126_39_15.D1 (m := 5) from colCertDiv_126_39_15.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 15 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T126_39_2 = colFn colCertDiv_126_39_15.D2 (m := 5) from colCertDiv_126_39_15.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_39_15_match


theorem leaf_126_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T126_39
      hfix126_39 hinj126_39 hcardT126_39
      (fun i => conj_mem_of_fixedPoints _ _ (T126_39 i) (hfix126_39 i) _)
      ⟨126, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T126_39_2 Q2.hfix126_39_2 Q2.hinj126_39_2
      Q2.hcardT126_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_39_2 i) (Q2.hfix126_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T126_39 = colFn colCertDiv_126_39_20.D1 (m := 5) from colCertDiv_126_39_20.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 20 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T126_39_2 = colFn colCertDiv_126_39_20.D2 (m := 5) from colCertDiv_126_39_20.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_39_20_match


theorem leaf_126_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T126_45
      hfix126_45 hinj126_45 hcardT126_45
      (fun i => conj_mem_of_fixedPoints _ _ (T126_45 i) (hfix126_45 i) _)
      ⟨126, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T126_45_2 Q2.hfix126_45_2 Q2.hinj126_45_2
      Q2.hcardT126_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_45_2 i) (Q2.hfix126_45_2 i) _)
      colCert_126_45_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T126_45
      hfix126_45 hinj126_45 hcardT126_45
      (fun i => conj_mem_of_fixedPoints _ _ (T126_45 i) (hfix126_45 i) _)
      ⟨126, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T126_45_2 Q2.hfix126_45_2 Q2.hinj126_45_2
      Q2.hcardT126_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_45_2 i) (Q2.hfix126_45_2 i) _)
      colCert_126_45_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T126_45
      hfix126_45 hinj126_45 hcardT126_45
      (fun i => conj_mem_of_fixedPoints _ _ (T126_45 i) (hfix126_45 i) _)
      ⟨126, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T126_45_2 Q2.hfix126_45_2 Q2.hinj126_45_2
      Q2.hcardT126_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_45_2 i) (Q2.hfix126_45_2 i) _)
      colCert_126_45_2.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T126_45
      hfix126_45 hinj126_45 hcardT126_45
      (fun i => conj_mem_of_fixedPoints _ _ (T126_45 i) (hfix126_45 i) _)
      ⟨126, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T126_45_2 Q2.hfix126_45_2 Q2.hinj126_45_2
      Q2.hcardT126_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_45_2 i) (Q2.hfix126_45_2 i) _)
      colCert_126_45_3.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T126_45
      hfix126_45 hinj126_45 hcardT126_45
      (fun i => conj_mem_of_fixedPoints _ _ (T126_45 i) (hfix126_45 i) _)
      ⟨126, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T126_45_2 Q2.hfix126_45_2 Q2.hinj126_45_2
      Q2.hcardT126_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_45_2 i) (Q2.hfix126_45_2 i) _)
      colCert_126_45_4.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T126_45
      hfix126_45 hinj126_45 hcardT126_45
      (fun i => conj_mem_of_fixedPoints _ _ (T126_45 i) (hfix126_45 i) _)
      ⟨126, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T126_45_2 Q2.hfix126_45_2 Q2.hinj126_45_2
      Q2.hcardT126_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_45_2 i) (Q2.hfix126_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T126_45 = colFn colCertDiv_126_45_5.D1 (m := 5) from colCertDiv_126_45_5.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 5 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T126_45_2 = colFn colCertDiv_126_45_5.D2 (m := 5) from colCertDiv_126_45_5.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_45_5_match


theorem leaf_126_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T126_45
      hfix126_45 hinj126_45 hcardT126_45
      (fun i => conj_mem_of_fixedPoints _ _ (T126_45 i) (hfix126_45 i) _)
      ⟨126, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T126_45_2 Q2.hfix126_45_2 Q2.hinj126_45_2
      Q2.hcardT126_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_45_2 i) (Q2.hfix126_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T126_45 = colFn colCertDiv_126_45_10.D1 (m := 5) from colCertDiv_126_45_10.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 10 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T126_45_2 = colFn colCertDiv_126_45_10.D2 (m := 5) from colCertDiv_126_45_10.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_45_10_match


theorem leaf_126_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T126_45
      hfix126_45 hinj126_45 hcardT126_45
      (fun i => conj_mem_of_fixedPoints _ _ (T126_45 i) (hfix126_45 i) _)
      ⟨126, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T126_45_2 Q2.hfix126_45_2 Q2.hinj126_45_2
      Q2.hcardT126_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_45_2 i) (Q2.hfix126_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T126_45 = colFn colCertDiv_126_45_15.D1 (m := 5) from colCertDiv_126_45_15.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 15 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T126_45_2 = colFn colCertDiv_126_45_15.D2 (m := 5) from colCertDiv_126_45_15.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_45_15_match


theorem leaf_126_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨126, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T126_45
      hfix126_45 hinj126_45 hcardT126_45
      (fun i => conj_mem_of_fixedPoints _ _ (T126_45 i) (hfix126_45 i) _)
      ⟨126, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T126_45_2 Q2.hfix126_45_2 Q2.hinj126_45_2
      Q2.hcardT126_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_45_2 i) (Q2.hfix126_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨126, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T126_45 = colFn colCertDiv_126_45_20.D1 (m := 5) from colCertDiv_126_45_20.bind1,
    show colData2 (⟨126, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 20 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T126_45_2 = colFn colCertDiv_126_45_20.D2 (m := 5) from colCertDiv_126_45_20.bind2]
  rw [alnId_126 j hj]
  exact fastcode_of_div ⟨126, by decide⟩ _ _ _
    ((alnId_126 j hj) ▸ Q2.listedAt (⟨126, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨126, by decide⟩ : Fin 148) hj hq).1) colCertDiv_126_45_20_match


theorem leaf_126_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T126_48
      hfix126_48 hinj126_48 hcardT126_48
      (fun i => conj_mem_of_fixedPoints _ _ (T126_48 i) (hfix126_48 i) _)
      ⟨126, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T126_48_2 Q2.hfix126_48_2 Q2.hinj126_48_2
      Q2.hcardT126_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_48_2 i) (Q2.hfix126_48_2 i) _)
      colCert_126_48_0.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T126_48
      hfix126_48 hinj126_48 hcardT126_48
      (fun i => conj_mem_of_fixedPoints _ _ (T126_48 i) (hfix126_48 i) _)
      ⟨126, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T126_48_2 Q2.hfix126_48_2 Q2.hinj126_48_2
      Q2.hcardT126_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_48_2 i) (Q2.hfix126_48_2 i) _)
      colCert_126_48_1.hD ?_).symm
  rw [alnId_126 j hj]


theorem leaf_126_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 126 []).length)
    (hq : (normIsRep.getD 126 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨126, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨126, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨126, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨126, by decide⟩ (listedAt ⟨126, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T126_48
      hfix126_48 hinj126_48 hcardT126_48
      (fun i => conj_mem_of_fixedPoints _ _ (T126_48 i) (hfix126_48 i) _)
      ⟨126, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨126, by decide⟩ (Q2.listedAt ⟨126, by decide⟩
        (alnCheck_rep ⟨126, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T126_48_2 Q2.hfix126_48_2 Q2.hinj126_48_2
      Q2.hcardT126_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T126_48_2 i) (Q2.hfix126_48_2 i) _)
      colCert_126_48_2.hD ?_).symm
  rw [alnId_126 j hj]


end LeanDring.P5Presentation
